; ModuleID = "/tmp/tensor_shr_x86_depth2_misaal__capture_50ae30bb64b4debd"
target triple = "unknown-unknown-unknown"
target datalayout = ""

define <16 x i32> @hydride.node.tensor_shr_x86_depth2_misaal__capture_50ae30bb64b4debd.0(<64 x i8> %arg, <64 x i8> %arg.1)
{
entry:
  %0 = call <16 x i32> @llvm.hydride._mm512_srav_epi16_dsl(<64 x i8> %arg.1, <1 x i32> <i32 0>, <64 x i8> %arg, <1 x i32> <i32 4294967295>, <1 x i1> <i1 1>, <1 x i32> <i32 32>, i32 512, i32 512, i32 0, i32 512, i32 32, i32 0, i32 32, i32 32, i32 1, i32 0)
  ret <16 x i32> %0
}

declare <16 x i32> @llvm.hydride._mm512_srav_epi16_dsl(<64 x i8> %arg, <1 x i32> %arg.1, <64 x i8> %arg.2, <1 x i32> %arg.3, <1 x i1> %arg.4, <1 x i32> %arg.5, i32 %arg.6, i32 %arg.7, i32 %arg.8, i32 %arg.9, i32 %arg.10, i32 %arg.11, i32 %arg.12, i32 %arg.13, i32 %arg.14, i32 %arg.15)

define dso_local <8 x i64> @_mm512_srav_epi32_wrapper(<8 x i64> %0, <8 x i64> %1) #2 {
  %3 = alloca <8 x i64>, align 64
  %4 = alloca <8 x i64>, align 64
  %5 = alloca <8 x i64>, align 64
  %6 = alloca <8 x i64>, align 64
  store <8 x i64> %0, <8 x i64>* %5, align 64
  store <8 x i64> %1, <8 x i64>* %6, align 64
  %7 = load <8 x i64>, <8 x i64>* %5, align 64
  %8 = load <8 x i64>, <8 x i64>* %6, align 64
  store <8 x i64> %7, <8 x i64>* %3, align 64
  store <8 x i64> %8, <8 x i64>* %4, align 64
  %9 = load <8 x i64>, <8 x i64>* %3, align 64
  %10 = bitcast <8 x i64> %9 to <16 x i32>
  %11 = load <8 x i64>, <8 x i64>* %4, align 64
  %12 = bitcast <8 x i64> %11 to <16 x i32>
  %13 = call <16 x i32> @llvm.x86.avx512.psrav.d.512(<16 x i32> %10, <16 x i32> %12) #6
  %14 = bitcast <16 x i32> %13 to <8 x i64>
  ret <8 x i64> %14
}

define dso_local <4 x i64> @_mm256_srav_epi32_wrapper(<4 x i64> %0, <4 x i64> %1) #0 {
  %3 = alloca <4 x i64>, align 32
  %4 = alloca <4 x i64>, align 32
  %5 = alloca <4 x i64>, align 32
  %6 = alloca <4 x i64>, align 32
  store <4 x i64> %0, <4 x i64>* %5, align 32
  store <4 x i64> %1, <4 x i64>* %6, align 32
  %7 = load <4 x i64>, <4 x i64>* %5, align 32
  %8 = load <4 x i64>, <4 x i64>* %6, align 32
  store <4 x i64> %7, <4 x i64>* %3, align 32
  store <4 x i64> %8, <4 x i64>* %4, align 32
  %9 = load <4 x i64>, <4 x i64>* %3, align 32
  %10 = bitcast <4 x i64> %9 to <8 x i32>
  %11 = load <4 x i64>, <4 x i64>* %4, align 32
  %12 = bitcast <4 x i64> %11 to <8 x i32>
  %13 = call <8 x i32> @llvm.x86.avx2.psrav.d.256(<8 x i32> %10, <8 x i32> %12) #6
  %14 = bitcast <8 x i32> %13 to <4 x i64>
  ret <4 x i64> %14
}

define dso_local <2 x i64> @_mm_srav_epi32_wrapper(<2 x i64> %0, <2 x i64> %1) #1 {
  %3 = alloca <2 x i64>, align 16
  %4 = alloca <2 x i64>, align 16
  %5 = alloca <2 x i64>, align 16
  %6 = alloca <2 x i64>, align 16
  store <2 x i64> %0, <2 x i64>* %5, align 16
  store <2 x i64> %1, <2 x i64>* %6, align 16
  %7 = load <2 x i64>, <2 x i64>* %5, align 16
  %8 = load <2 x i64>, <2 x i64>* %6, align 16
  store <2 x i64> %7, <2 x i64>* %3, align 16
  store <2 x i64> %8, <2 x i64>* %4, align 16
  %9 = load <2 x i64>, <2 x i64>* %3, align 16
  %10 = bitcast <2 x i64> %9 to <4 x i32>
  %11 = load <2 x i64>, <2 x i64>* %4, align 16
  %12 = bitcast <2 x i64> %11 to <4 x i32>
  %13 = call <4 x i32> @llvm.x86.avx2.psrav.d(<4 x i32> %10, <4 x i32> %12) #6
  %14 = bitcast <4 x i32> %13 to <2 x i64>
  ret <2 x i64> %14
}

declare <16 x i32> @llvm.x86.avx512.psrav.d.512(<16 x i32>, <16 x i32>) #4

declare <4 x i32> @llvm.x86.avx2.psrav.d(<4 x i32>, <4 x i32>) #4

declare <8 x i32> @llvm.x86.avx2.psrav.d.256(<8 x i32>, <8 x i32>) #4

attributes #0 = { noinline nounwind optnone uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="256" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="cascadelake" "target-features"="+64bit,+adx,+aes,+avx,+avx2,+avx512bw,+avx512cd,+avx512dq,+avx512f,+avx512ifma,+avx512vl,+avx512vnni,+bmi,+bmi2,+clflushopt,+clwb,+cmov,+cx16,+cx8,+f16c,+fma,+fsgsbase,+fxsr,+invpcid,+lzcnt,+mmx,+movbe,+pclmul,+pku,+popcnt,+prfchw,+rdrnd,+rdseed,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave,+xsavec,+xsaveopt,+xsaves,-amx-bf16,-amx-int8,-amx-tile,-avx512bf16,-avx512bitalg,-avx512er,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-cldemote,-clzero,-enqcmd,-fma4,-gfni,-hreset,-kl,-lwp,-movdir64b,-movdiri,-mwaitx,-pconfig,-prefetchwt1,-ptwrite,-rdpid,-rtm,-serialize,-sgx,-sha,-shstk,-sse4a,-tbm,-tsxldtrk,-uintr,-vaes,-vpclmulqdq,-waitpkg,-wbnoinvd,-widekl,-xop" "unsafe-fp-math"="false" "use-soft-float"="false" }

attributes #1 = { noinline nounwind optnone uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="128" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="cascadelake" "target-features"="+64bit,+adx,+aes,+avx,+avx2,+avx512bw,+avx512cd,+avx512dq,+avx512f,+avx512ifma,+avx512vl,+avx512vnni,+bmi,+bmi2,+clflushopt,+clwb,+cmov,+cx16,+cx8,+f16c,+fma,+fsgsbase,+fxsr,+invpcid,+lzcnt,+mmx,+movbe,+pclmul,+pku,+popcnt,+prfchw,+rdrnd,+rdseed,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave,+xsavec,+xsaveopt,+xsaves,-amx-bf16,-amx-int8,-amx-tile,-avx512bf16,-avx512bitalg,-avx512er,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-cldemote,-clzero,-enqcmd,-fma4,-gfni,-hreset,-kl,-lwp,-movdir64b,-movdiri,-mwaitx,-pconfig,-prefetchwt1,-ptwrite,-rdpid,-rtm,-serialize,-sgx,-sha,-shstk,-sse4a,-tbm,-tsxldtrk,-uintr,-vaes,-vpclmulqdq,-waitpkg,-wbnoinvd,-widekl,-xop" "unsafe-fp-math"="false" "use-soft-float"="false" }

attributes #2 = { noinline nounwind optnone uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="512" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="cascadelake" "target-features"="+64bit,+adx,+aes,+avx,+avx2,+avx512bw,+avx512cd,+avx512dq,+avx512f,+avx512ifma,+avx512vl,+avx512vnni,+bmi,+bmi2,+clflushopt,+clwb,+cmov,+cx16,+cx8,+f16c,+fma,+fsgsbase,+fxsr,+invpcid,+lzcnt,+mmx,+movbe,+pclmul,+pku,+popcnt,+prfchw,+rdrnd,+rdseed,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave,+xsavec,+xsaveopt,+xsaves,-amx-bf16,-amx-int8,-amx-tile,-avx512bf16,-avx512bitalg,-avx512er,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-cldemote,-clzero,-enqcmd,-fma4,-gfni,-hreset,-kl,-lwp,-movdir64b,-movdiri,-mwaitx,-pconfig,-prefetchwt1,-ptwrite,-rdpid,-rtm,-serialize,-sgx,-sha,-shstk,-sse4a,-tbm,-tsxldtrk,-uintr,-vaes,-vpclmulqdq,-waitpkg,-wbnoinvd,-widekl,-xop" "unsafe-fp-math"="false" "use-soft-float"="false" }

attributes #4 = { nounwind readnone }

attributes #6 = { nounwind }
