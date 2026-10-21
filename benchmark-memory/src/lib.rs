//! Native allocation protection for the two benchmark executables.
//!
//! Call [`configure`] before parsing workload arguments or constructing an egraph.
//! On macOS this bounds additional VM above the startup mapping size; on Linux
//! it bounds total VM. Existing macOS mappings can become resident without new
//! VM, so neither policy is an aggregate RSS or process-group memory guarantee.

use std::alloc::{GlobalAlloc, Layout};
use std::ffi::OsString;
use std::sync::atomic::{AtomicBool, Ordering};

const ALLOCATION_EXIT: i32 = 86;
const SETUP_EXIT: i32 = 87;
// Mimalloc reads these before main. Disallow startup reservations that could
// become resident without requesting more VM after the limit is installed.
const ALLOCATOR_ENV: [(&str, &str); 4] = [
    ("MIMALLOC_ARENA_RESERVE", "0"),
    ("MIMALLOC_DISALLOW_ARENA_ALLOC", "1"),
    ("MIMALLOC_RESERVE_OS_MEMORY", "0"),
    ("MIMALLOC_RESERVE_HUGE_OS_PAGES", "0"),
];
static LIMITED: AtomicBool = AtomicBool::new(false);

#[cfg(test)]
#[global_allocator]
static ALLOCATOR: LimitedAllocator = LimitedAllocator;

/// Mimalloc with a distinct allocation-failure exit after native protection is installed.
/// The executable opts into this allocator; library consumers retain their allocator.
pub struct LimitedAllocator;

// The wrapper preserves mimalloc's contracts, but exits without further allocation
// if allocation fails after the native limit was installed. No unwinding is safe
// inside a global allocator, and the fixed exit identifies exhaustion independently of diagnostics.
unsafe impl GlobalAlloc for LimitedAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        allocation_result(unsafe { mimalloc::MiMalloc.alloc(layout) })
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        allocation_result(unsafe { mimalloc::MiMalloc.alloc_zeroed(layout) })
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        allocation_result(unsafe { mimalloc::MiMalloc.realloc(pointer, layout, size) })
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { mimalloc::MiMalloc.dealloc(pointer, layout) }
    }
}

fn allocation_result(pointer: *mut u8) -> *mut u8 {
    if pointer.is_null() && LIMITED.load(Ordering::Relaxed) {
        let message = b"native memory limit: allocation failed under limit; stopping workload\n";
        // write and _exit do not allocate or run destructors. Partial diagnostic
        // writes are harmless: the reserved exit status remains authoritative.
        unsafe {
            libc::write(2, message.as_ptr().cast(), message.len() as _);
            libc::_exit(ALLOCATION_EXIT);
        }
    }
    pointer
}

/// Consume the optional native limit before either executable handles its input.
///
/// The explicit flag also makes older binaries reject guarded invocations instead
/// of silently ignoring an environment variable. Invalid requests and unsupported
/// platforms exit with status 87; allocation exhaustion after setup exits with 86.
#[must_use]
pub fn configure(args: impl IntoIterator<Item = OsString>) -> Vec<OsString> {
    let result = parse_arguments(args).and_then(|(args, limit)| {
        if let Some(limit) = limit {
            install_limit(limit)?;
        }
        Ok(args)
    });
    result.unwrap_or_else(|error| {
        eprintln!("native memory limit: {error}");
        std::process::exit(SETUP_EXIT);
    })
}

fn parse_arguments(
    args: impl IntoIterator<Item = OsString>,
) -> Result<(Vec<OsString>, Option<u64>), String> {
    let mut args = args.into_iter();
    let mut filtered = vec![args.next().ok_or("missing executable name")?];
    let mut limit = None;
    while let Some(arg) = args.next() {
        if arg == "--" {
            filtered.push(arg);
            filtered.extend(args);
            break;
        }
        let value = if arg == "--memory-limit-bytes" {
            Some(args.next().ok_or("--memory-limit-bytes requires a value")?)
        } else {
            arg.to_str()
                .and_then(|arg| arg.strip_prefix("--memory-limit-bytes="))
                .map(OsString::from)
        };
        if let Some(value) = value {
            if limit.is_some() {
                return Err("--memory-limit-bytes may only be specified once".into());
            }
            let value = value
                .to_str()
                .filter(|value| {
                    !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())
                })
                .and_then(|value| value.parse::<u64>().ok())
                .filter(|value| *value > 0)
                .ok_or("--memory-limit-bytes must be a positive integer")?;
            limit = Some(value);
        } else {
            filtered.push(arg);
        }
    }
    Ok((filtered, limit))
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn install_limit(bytes: u64) -> Result<(), String> {
    for (name, value) in ALLOCATOR_ENV {
        if std::env::var(name).as_deref() != Ok(value) {
            return Err(format!(
                "set {name}={value} before launching the native-limited executable"
            ));
        }
    }
    #[cfg(target_os = "macos")]
    let bytes = virtual_size()?
        .checked_add(bytes)
        .ok_or("address-space limit overflow")?;
    // Restrict both limits, respecting a stricter inherited limit. Setting this
    // after exec is necessary on macOS because dyld reserves huge fixed mappings.
    let mut limit: libc::rlimit = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &mut limit) } != 0 {
        return Err(format!(
            "getrlimit(RLIMIT_AS): {}",
            std::io::Error::last_os_error()
        ));
    }
    let requested = libc::rlim_t::try_from(bytes)
        .map_err(|_| "address-space limit does not fit the platform limit type")?;
    if requested == libc::RLIM_INFINITY {
        return Err("address-space limit must be finite".into());
    }
    let cap = requested.min(limit.rlim_cur).min(limit.rlim_max);
    limit.rlim_cur = cap;
    limit.rlim_max = cap;
    if unsafe { libc::setrlimit(libc::RLIMIT_AS, &limit) } != 0 {
        return Err(format!(
            "setrlimit(RLIMIT_AS): {}",
            std::io::Error::last_os_error()
        ));
    }
    let mut installed: libc::rlimit = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &mut installed) } != 0
        || installed.rlim_cur != cap
        || installed.rlim_max != cap
    {
        return Err("could not verify installed address-space limit".into());
    }
    LIMITED.store(true, Ordering::Relaxed);
    Ok(())
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn install_limit(_bytes: u64) -> Result<(), String> {
    Err("native address-space protection is supported only on macOS and Linux".into())
}

#[cfg(target_os = "macos")]
fn virtual_size() -> Result<u64, String> {
    #[allow(deprecated)]
    let task = unsafe { libc::mach_task_self() };
    let mut info: libc::mach_task_basic_info = unsafe { std::mem::zeroed() };
    let mut count = libc::MACH_TASK_BASIC_INFO_COUNT;
    let result = unsafe {
        libc::task_info(
            task,
            libc::MACH_TASK_BASIC_INFO,
            (&mut info as *mut libc::mach_task_basic_info).cast(),
            &mut count,
        )
    };
    if result != libc::KERN_SUCCESS || count != libc::MACH_TASK_BASIC_INFO_COUNT {
        return Err(format!(
            "could not inspect startup VM size (Mach status {result})"
        ));
    }
    Ok(info.virtual_size)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;

    #[test]
    fn inactive_allocator_preserves_null() {
        assert!(allocation_result(std::ptr::null_mut()).is_null());
    }

    #[test]
    fn parses_limit_before_workload_arguments() {
        let (args, limit) =
            parse_arguments(["bin", "--memory-limit-bytes=1024", "input.egg"].map(OsString::from))
                .unwrap();
        assert_eq!(args, ["bin", "input.egg"].map(OsString::from));
        assert_eq!(limit, Some(1024));
        assert_eq!(
            parse_arguments(["bin", "--memory-limit-bytes=10737418241"].map(OsString::from))
                .unwrap()
                .1,
            Some(10737418241)
        );
        let args = ["bin", "--", "--memory-limit-bytes=1024"].map(OsString::from);
        assert_eq!(
            parse_arguments(args.clone()).unwrap(),
            (args.to_vec(), None)
        );
        for args in [
            vec!["bin", "--memory-limit-bytes"],
            vec!["bin", "--memory-limit-bytes=0"],
            vec!["bin", "--memory-limit-bytes=-1"],
            vec!["bin", "--memory-limit-bytes=+1"],
            vec!["bin", "--memory-limit-bytes=18446744073709551616"],
            vec!["bin", "--memory-limit-bytes=1", "--memory-limit-bytes=2"],
        ] {
            assert!(parse_arguments(args.into_iter().map(OsString::from)).is_err());
        }
    }

    #[test]
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn allocation_limit_stops_small_large_zeroed_and_reallocated_blocks() {
        for operation in ["small", "large", "zeroed", "realloc"] {
            let output = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "tests::allocation_child", "--nocapture"])
                .env("BENCHMARK_MEMORY_TEST_CHILD", operation)
                .envs(ALLOCATOR_ENV)
                .output()
                .unwrap();
            assert_eq!(
                output.status.code(),
                Some(ALLOCATION_EXIT),
                "{operation}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(String::from_utf8_lossy(&output.stderr).contains("allocation failed"));
        }
    }

    #[test]
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn setup_fails_closed_and_preserves_inherited_limits() {
        for scenario in ["missing-env", "invalid-limit", "inherited-limit"] {
            let mut command = Command::new(std::env::current_exe().unwrap());
            command
                .args(["--exact", "tests::configuration_child", "--nocapture"])
                .env("BENCHMARK_MEMORY_TEST_CHILD", scenario)
                .envs(ALLOCATOR_ENV);
            if scenario == "missing-env" {
                command.env_remove("MIMALLOC_RESERVE_OS_MEMORY");
            }
            let output = command.output().unwrap();
            let expected = if scenario == "inherited-limit" {
                0
            } else {
                SETUP_EXIT
            };
            assert_eq!(
                output.status.code(),
                Some(expected),
                "{scenario}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }

    #[test]
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn configuration_child() {
        let Ok(scenario) = std::env::var("BENCHMARK_MEMORY_TEST_CHILD") else {
            return;
        };
        if scenario != "inherited-limit" {
            let value = if scenario == "invalid-limit" {
                "0"
            } else {
                "33554432"
            };
            let _ = configure(["bin", "--memory-limit-bytes", value].map(OsString::from));
            panic!("invalid native limit configuration was accepted");
        }
        #[cfg(target_os = "macos")]
        let baseline = virtual_size().unwrap();
        #[cfg(target_os = "linux")]
        let baseline = {
            let status = std::fs::read_to_string("/proc/self/statm").unwrap();
            status
                .split_whitespace()
                .next()
                .unwrap()
                .parse::<u64>()
                .unwrap()
                * unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as u64
        };
        let mut original: libc::rlimit = unsafe { std::mem::zeroed() };
        assert_eq!(
            unsafe { libc::getrlimit(libc::RLIMIT_AS, &mut original) },
            0
        );
        let inherited = libc::rlim_t::try_from(baseline + 32 * 1024 * 1024)
            .unwrap()
            .min(original.rlim_cur)
            .min(original.rlim_max);
        original.rlim_cur = inherited;
        assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_AS, &original) }, 0);
        // The requested limit is larger, but neither soft nor hard is raised.
        install_limit(10 * 1024 * 1024 * 1024).unwrap();
        assert_eq!(
            unsafe { libc::getrlimit(libc::RLIMIT_AS, &mut original) },
            0
        );
        assert_eq!(original.rlim_cur, inherited);
        assert_eq!(original.rlim_max, inherited);
    }

    #[test]
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn allocation_child() {
        let Ok(operation) = std::env::var("BENCHMARK_MEMORY_TEST_CHILD") else {
            return;
        };
        const MIB: usize = 1024 * 1024;
        #[cfg(target_os = "macos")]
        let bytes = 32 * MIB as u64;
        #[cfg(target_os = "linux")]
        let bytes = {
            // The harness has already created a thread stack; give this bounded
            // subprocess just 32 MiB above its current virtual address space.
            let status = std::fs::read_to_string("/proc/self/statm").unwrap();
            status
                .split_whitespace()
                .next()
                .unwrap()
                .parse::<u64>()
                .unwrap()
                * unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as u64
                + 32 * MIB as u64
        };
        install_limit(bytes).unwrap();
        // Kernel enforcement is checked without touching the oversized mapping.
        let mapping = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                64 * MIB,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            )
        };
        assert_eq!(mapping, libc::MAP_FAILED);
        let block = if operation == "small" { 4096 } else { MIB };
        // Independent bound: even a broken native limit touches at most 128 MiB.
        for _ in 0..128 * MIB / block {
            let layout = Layout::from_size_align(block, 16).unwrap();
            unsafe {
                let pointer = match operation.as_str() {
                    "zeroed" => ALLOCATOR.alloc_zeroed(layout),
                    "realloc" => {
                        let initial = Layout::from_size_align(16, 16).unwrap();
                        ALLOCATOR.realloc(ALLOCATOR.alloc(initial), initial, block)
                    }
                    _ => ALLOCATOR.alloc(layout),
                };
                assert!(!pointer.is_null());
                std::hint::black_box(pointer).write_bytes(1, block);
            }
        }
        panic!("native limit did not stop the independently bounded allocation probe");
    }
}
