# Independent Add/Sub oracle: prediction before compiler probe

2026-10-18. This artifact predicts source arithmetic only. No EggCC optimization, native compilation or model invocation is part of this oracle run.

At signed i64 MAX, in the reached `0 < x` arm, `x+1` is MIN modulo 2^64 and `x+1<0` is true. At MAX−1, 2 and 1 the answer is false; at 0 and −1 the print is skipped and its complete expected stdout is the present empty string.

At signed i64 MIN, in the reached `x < 0` arm, `x−1` is MAX modulo 2^64 and `0<x−1` is true. At MIN+1, −2 and −1 the answer is false; at 0 and 1 the print is skipped and its complete expected stdout is the present empty string.

These predictions follow exact mathematical integer addition/subtraction, Euclidean remainder modulo 2^64, then signed decoding. The script independently crosschecks a bit-by-bit full-adder model and predetermined endpoint values. Missing/null output is missing evidence and never matches a skipped print. This says nothing yet about an actual compiler rule firing, bad union, native output, detector conflict or new bug.

Supplied source: EggCC object `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, `dag_in_context/src/interpreter.rs:239–244`, uses `wrapping_add` and `wrapping_sub`. Full interpreter blob SHA-256: `dd991459c2baa77f52ba03a0533147c4b134a2da0ed343f105cb049e415f0491`. Fixture bodies follow the approved consumer note's proposed Bril; syntax/type/native admission belongs to the compiler owner. Independent oracle fixtures are not claimed parser-tested.

Confirming oracle prediction: endpoint true, nearby false, skipped controls present-empty, with agreement between exact modulo and elementary bit addition. Disconfirming prediction: either model or a hardcoded endpoint expectation disagrees; retain failure and revise the oracle before it supplies compiler acceptance. Compiler U0/native parity and the prospective encoding probe are separate later experiments.
