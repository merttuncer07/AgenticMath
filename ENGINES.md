# Engines: the training wheels, and the road to our own

AgenticMath uses the best existing engines now, so agents get state-of-the-art answers from the first release.
They are training wheels. The goal is an independent implementation of every piece, each one replacing an
engine only when it matches it on correctness (differential tests on random problems, the engine as oracle) and
comes close on speed (benchmarks on real sizes).

## Rules
- Engine calls stay behind a small internal seam; the language, the account (status, facts, work) and the agent
  interface are ours from the start.
- When we write our own version of a function, the engine's version stays in the build as the oracle until the
  differential tests pass; then the engine call is removed.
- Upstream bugs found on the way are worked around, written down here, and reported.

## Ledger
| Function | Engine now | Our own | Notes |
|---|---|---|---|
| parsing, values, printing, status/facts/work, JSON | ours | yes | |
| rules, patterns, conditions, recursion, the library (lib/*.am) | ours | yes | the place where breadth grows |
| function terms (kernels), chain rule, subs through them | ours | yes | on FLINT's polynomial arithmetic |
| MCP server, JSON reader, reference, name suggestions | ours | yes | |
| integrate: Hermite, Rothstein-Trager driver, LogToAtan, by parts, rules, check by differentiation | ours | yes | uses FLINT for polynomial gcd, resultants, factoring; Calcium for algebraic gcds |
| normal form and zero test (trig, sqrt), certified witnesses | ours | yes | Arb for certified evaluation |
| series, limits (with log symbols and exponential dominance), definite integrals | ours | yes | |
| certified numerical integration | Arb (acb_calc_integrate) | no | our ball evaluator of expressions feeds it |
| linear algebra (Gaussian elimination over our values), sums, ODEs | ours | yes | |
| number theory (powmod, nextprime, totient, ...) | FLINT fmpz | no | |
| cofactors (ideal membership by Macaulay matrices), Lean 4 certificates | ours | yes | FLINT for the rational linear algebra |
| big integers | GMP (through FLINT) | no | the deepest layer; decided last |
| rational functions in many variables | FLINT fmpz_mpoly_q | no | |
| factor (whole numbers) | FLINT fmpz_factor, fmpz_is_prime | no | primality proofs |
| factor (polynomials) | FLINT fmpz_mpoly_factor | no | univariate: Zassenhaus + van Hoeij; multivariate: Wang, Zippel |
| gcd, resultant, discriminant, diff | FLINT fmpz_mpoly | no | |
| exact numbers (sqrt, pi, exp, log, trig) | Calcium (in FLINT) | no | exact zero tests |
| algebraic numbers, roots | FLINT qqbar | no | |
| N (certified decimals) | Arb/Calcium | no | |
| solve (systems) | msolve (F4, multi-modular, rational parametrization) | no | run in a child process; GPL-2+ |
| solution check | ours (exact substitution) | yes | |

## Upstream issues
- FLINT 3.3.1: `ca_fmpz_poly_evaluate` returns 0 when the point lies in a number field (e.g. (1 + sqrt(3))/2
  in 16t^3 - 16t). We use Horner's rule with ca arithmetic instead. To report.
- msolve 0.9.0, `msolve_julia`: calls `exit(1)` on failure and reads `gens` after freeing it; hence the child
  process.
- msolve 0.9.0 build: `configure` detects the building machine's vector extensions (up to AVX-512) and the
  sources use them under `HAVE_AVX2`/`HAVE_AVX512_F`, so a static binary built on one machine dies with an
  illegal instruction on another. We answer the detection with `ax_cv_have_avx_os_support_ext=no
  ax_cv_have_avx512_os_support_ext=no` and pass SSE flags only (Makefile, `MSOLVE_FLAGS`). A build option for
  portable binaries would help upstream; our own Gröbner engine should dispatch at run time instead.
