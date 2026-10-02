# AgenticMath

A mathematics language whose first user is an AI agent. One static binary, `amath`: nothing to install, nothing
written to disk. Every answer gives an account of itself.

    $ amath -e 'factor(x^4 - 1)'
    (x - 1)*(x + 1)*(x^2 + 1)  [proved: every factor proved irreducible over Q (complete univariate factorization); multiplied back]

    $ amath -j -e 'factor(x^4 - 1)'
    {"input":"factor(x^4 - 1)","answer":"(x - 1)*(x + 1)*(x^2 + 1)","status":"proved","verdict":"...",
     "facts":{"irreducible":false,"squarefree":true,"factor_degrees":[1,1,2],"multiplicities":[1,1,1],"rational_roots":["1","-1"]}}

## For agents: `amath --mcp`
A Model Context Protocol server, in the same binary. Add it to an agent's MCP configuration:

    {"mcpServers": {"agenticmath": {"command": "/path/to/amath", "args": ["--mcp"]}}}

Two tools:
- `evaluate` — `code`: statements, one per line (definitions persist for the session); `show`: also return the
  steps and rules applied; `max_chars`: cut long answers (default 4000; the facts give the full length).
  Returns one JSON object per statement.
- `reference` — the language: notation, statuses, every function's signature, the library rules; or one entry.

A misspelled or foreign function name stays symbolic and the facts suggest the right one
(`factr(12)` → `"did_you_mean":"factor"`; `evalf` → `N`). In the language itself, `help()` and `help(factor)`.

## The account of an answer
- `status`: how sure the answer is. `proved` (a complete argument was carried out), `exact` (exact arithmetic),
  `certified` (every digit guaranteed by ball arithmetic), `probable` (rests on a randomized step), `numeric`
  (no guarantee), `unknown` (could not be decided). An answer is as sure as its weakest step.
- `verdict`: the reason, in words.
- `facts`: what the computation produced anyway (no extra work to explain): degrees, multiplicities, number of
  real roots, number of solutions.
- `work`: with `show STATEMENT`, the steps actually taken.
- `error`: why it failed and, where known, what would be needed.

## Notation
What agents already write: `x^2` or `x**2`, `2x`, `3(x + 1)`, `sqrt`, `pi`, `E`, `I`, lists `[a, b]`, equations
`x^2 = 2`, tests `==`, `<`, names `a = ...`. Decimals are exact (`0.1` is 1/10). Multi-letter names are single
variables (`xy` is one variable).

## Defining mathematics in the language
Functions are defined by rules, and the library is written this way, so the language grows without growing its C
core.

    fact(0) := 1
    fact(n) := n*fact(n - 1) if n > 0          # a condition
    fib(n) := if(n < 2, n, fib(n - 1) + fib(n - 2))
    mylog(exp(u)) := u                         # a pattern: matches exp(...) and binds u
    h(x, y) = x*y + 1                          # = also defines, when the arguments are plain names
    map(sq, [1, 2, 3]),  L[2],  a and b,  not c

Rules are tried in the order written; the first whose patterns match and whose condition holds gives the value.
A rule for a built-in name is tried before the built-in, which is how `lib/prelude.am` teaches `diff` the
derivatives of sin, exp, log, ...:

    diff(sin(u), x) := cos(u)*diff(u, x)

`show` prints every rule as it is applied. A call that nothing evaluates stays symbolic (`f(x)`, `mylog(sin(x))`)
and the facts say so (`undefined_function`, `unevaluated`), so a misspelled name is noticed.

Function terms such as `sin(x)`, `exp(x^2)`, `f(x)`, and irrational numbers among variables (`sqrt(2)*x`) are
generators of the polynomial arithmetic: `2*sin(x) + sin(x)` is `3*sin(x)`, `diff(log(sin(x)), x)` is
`cos(x)/sin(x)`, `subs` and `N` look inside them. An equality the arithmetic cannot settle, such as
`sin(x)^2 + cos(x)^2 == 1`, answers `unknown`, never a guess.

## Integration
`integrate(f, x)` returns an antiderivative and checks it by differentiating it back; the status says how far
the check went (`proved`: the derivative equals the integrand exactly; `probable`: equal at random points;
`unknown`: not decided). What it does:
- rational functions exactly: polynomial part, Hermite reduction, Rothstein–Trager with exact algebraic
  coefficients, complex logarithms turned into real arctangents (Rioboo): `integrate(1/(x^3+1), x)` →
  `(2*sqrt(3)*atan((2*x - 1)/sqrt(3)) + 2*log(x + 1) - log(x^2 - x + 1))/6`;
- linearity and constant factors; a polynomial times exp, sin, cos (repeated integration by parts) or log, atan;
- the rules for `antiderivative` in `lib/integrate.am`, written in the language (exp, sin, cos, tan, log, atan,
  sqrt of a linear argument; exp·sin, exp·cos, sin·cos, sin², cos²; 1/sqrt and sqrt of a quadratic; exp of a
  quadratic through erf);
- powers of sin and cos by substitution and power reduction; powers of log by parts;
- substitution t = u for a function term or its argument when the integrand is g(u)·u':
  `integrate(1/(x*log(x)), x)` → `log(log(x))`, `integrate(1/(1+exp(x)), x)` → `x - log(exp(x) + 1)`,
  `integrate(x^3*exp(x^2), x)` → `(x^2*exp(x^2) - exp(x^2))/2`;
- what nothing finds stays as `integrate(...)`, with status `unknown` (`integrate(sin(x)/x, x)`).

Rules can match products and powers: `antiderivative(exp(u)*sin(v), x) := ... if linear(u, x) and linear(v, x)`.

## Series, limits, definite integrals
- `series(f, x, a, n)`: Taylor or Laurent series with exact coefficients, written in ascending powers with
  `O(...)`; the facts list the coefficients. `taylor(f, x, a, n)` gives the terms as an expression to compute with.
  `series(tan(x), x, 0, 8)` → `x + x^3/3 + 2*x^5/15 + 17*x^7/315 + O(x^8)`.
- `limit(f, x, a)` (a number, `oo` or `-oo`; `"+"` or `"-"` for one side): from the leading term of the series;
  log(x − a) is kept as a symbol, one-sided limits use x = a ± t² (so half powers become whole), and an
  exponential that is smaller or larger than every power dominates. `limit(x^x, x, 0, "+")` → 1,
  `limit((1+1/x)^x, x, oo)` → exp(1), `limit(x^5*exp(-x), x, oo)` → 0, `limit(1/x, x, 0)` → does not exist.
  Comparing two exponentials (`exp(x) - exp(2x)`) needs the full Gruntz algorithm and is refused for now.
- `integrate(f, x, a, b)`: F(b) − F(a) with limits at the ends, cross-checked against Arb's certified numerical
  integration; proved when the antiderivative is proved continuous on the interval: every square root, logarithm,
  arcsine and denominator in it is shown to stay in its domain (exactly from real roots when the condition is a
  polynomial, else by ball arithmetic on pieces). For an improper integral, continuity inside the interval and
  the one-sided limits at the ends: `integrate(log(x)^2, x, 0, 1)` → `2  [proved]`. A pole of a rational integrand on the interval proves divergence. With no
  antiderivative, the certified decimal is the answer: `integrate(exp(x^2), x, 0, 1)` →
  `1.46265174590718160880404858686  [certified]`. `integrate(1/(x^4+1), x, 0, oo)` → `pi*sqrt(2)/4  [proved]`.
- Powers with any exponent: `x^(1/2)` is `sqrt(x)`, `x^x` is `exp(x*log(x))`.

## Linear algebra, number theory, sums, differential equations
- Matrices are lists of rows: `A = [[1, 2], [3, 4]]`; `A*B`, `A*v`, `A^-1`, `det`, `inverse`, `transpose`, `rref`,
  `rank`, `nullspace`, `linsolve(A, b)` (every solution, with free parameters t1, t2, ..., or `[]`), `charpoly`,
  `eigenvals`, `eigenvects`, `trace`, `identity`, `dot`, `cross`; symbolic and algebraic entries.
- Whole numbers: `mod`, `powmod`, `invmod`, `gcd`, `lcm`, `divisors`, `nextprime`, `totient`, `crt`, `isprime`,
  `factor`, `fibonacci`, `lucas`, `bernoulli`, `partitions`, `binomial`, `n!`.
- `sum(f, k, a, b)`: term by term, or closed forms, each checked: polynomial terms (`sum(k^3, k, 1, n)` →
  `(n^4 + 2*n^3 + n^2)/4`), geometric terms (to `oo` when |r| < 1), hypergeometric terms by Gosper's algorithm
  (`sum(k*2^k, k, 1, n)` → `2*n*2^n - 2*2^n + 2`, `sum(1/(k*(k+1)), k, 1, oo)` → 1; when it fails, that is a proof
  that no hypergeometric closed form exists), p-series through `zeta` (`sum(1/k^2, k, 1, oo)` → `pi^2/6`), and the
  known hypergeometric series to infinity, identified from the term ratio: `sum(x^k/k!, k, 0, oo)` → `exp(x)`,
  `sum((-1)^k*x^(2k)/(2k)!, k, 0, oo)` → `cos(x)`, `sum((-1)^k/(2k+1), k, 0, oo)` → `pi/4`,
  `sum(x^k/k, k, 1, oo)` → `-log(-x + 1)` with the condition `|x| < 1` stated.
- `product(f, k, a, b)`; `factorial(n)` (also `n!`) for whole numbers, other numbers (gamma) and expressions.
- `zeta(s)`: exact for even s > 0 and s ≤ 0; otherwise a term whose digits `N` certifies.
- `dsolve(eq, y, x[, [y(0) = a, y'(0) = b]])`: linear equations with constant coefficients of any order (complex
  and repeated roots; right-hand sides by variation of parameters), first-order linear equations, and separable
  first-order equations (`dsolve(y' = x/y, y, x, [y(0) = 2])` → `y = sqrt(x^2 + 4)`; the implicit form when y
  cannot be isolated); `y'`, `y''` for derivatives; every solution put back into the equation. `dsolve(y'' + y = 1/cos(x), y, x)` →
  `y = x*sin(x) + cos(x)*log(cos(x)) + cos(x)*C1 + sin(x)*C2  [proved]`.
- Exponentials combine (`exp(x)*exp(-x)` is 1), `sin(-x)` is `-sin(x)`, and checks expand multiple angles.

## Certificates for Lean
`cofactors(g, [h1, ..., hk])` finds polynomials c_i with g = c₁h₁ + … + c_kh_k (so g = 0 follows from the
hypotheses), by linear algebra on the coefficients, and checks them by expansion. Prefix any statement with `lean`
and the facts carry a Lean 4 proof:

    lean cofactors(x^3 + y^3 = 0, [x + y = 0])
    example (x y : ℚ) (h1 : x + y = 0) :
        x^3 + y^3 = 0 := by
      linear_combination (x^2 - x*y + y^2) * h1

Also `lean factor(p)` (by ring), `lean a == b` for polynomial identities (by ring), `lean factor(n)` and
`lean isprime(p)` (by norm_num). With `AMATH_LEAN_PROJECT` set to a Lean 4 project with Mathlib, Lean checks each
proof and the facts say `lean_checked`; otherwise the proofs are generated but not run. This is the service Mathlib's
`polyrith` tactic used to get from an online Sage server, offline and in one file.

## Solving
- `solve(eq, x)`: polynomials with number coefficients exactly (every complex root, radicals when short, else
  `RootOf`); symbolic coefficients by formula up to degree 2 (`solve(a*x^2 + b*x + c = 0, x)`); an equation in one
  function term is solved for the term and inverted (exp, log, sqrt, sin, cos, tan and their inverses), periodic
  families with integer parameters: `solve(sin(x) = 1/2, x)` → `[x = (12*n1*pi + pi)/6, x = (12*n1*pi + 5*pi)/6]`,
  `solve(exp(x) = 5, x)` → `[x = 2*n1*pi*I + log(5)]` with the fact `real_solutions: ["x = log(5)"]`. Every
  candidate is put back into the equation; false branches are dropped. `==` is read as `=` inside `solve`.
- `solve([eqs], [vars])`: polynomial systems via msolve, each solution exact and checked.
- `solve(p < q, x)` (`<=`, `>`, `>=`): rational inequalities, exactly: `solve(x^3 - x > 0, x)` → `-1 < x < 0 or x > 1`.
- `nsolve(eq, x, a, b[, digits])`: every real root in [a, b], certified by Arb root isolation:
  `nsolve(x*exp(x) = 1, x, -10, 10)` → `[x = 0.567143290409784]  [certified]`.
- `apart(f, x)`: partial fractions over Q, checked by adding them back.

## Deciding equality
`a == b` subtracts and decides: exact arithmetic for numbers; for expressions, a normal form (tan = sin/cos,
sin² + cos² = 1, sqrt(u)² = u, sqrt(D)² = D, I² = −1) that proves equality when the difference reduces to 0; a
point where the sides differ, found by certified evaluation, proves `false`; equality at random points gives
`true` only with status `probable`.

## Functions
| | |
|---|---|
| arithmetic | exact rationals, algebraic numbers, pi, E, I; rational functions in up to 32 variables |
| `factor(n)`, `factor(p)` | whole numbers and fractions (primes proved); polynomials in one or many variables |
| `roots(p)`, `realroots(p)` | every root as an exact algebraic number (`sqrt(2)`, `RootOf(x^3 - x - 1, 1.32472)`) |
| `solve`, `nsolve`, `apart` | see Solving |
| `N(x, digits)` | decimals with every digit guaranteed (also for `zeta(3) + pi` and other constant terms) |
| `diff`, `gcd`, `resultant`, `discriminant`, `degree`, `subs`, `numer`, `denom`, `binomial`, `isprime` | |
| `sqrt exp log sin cos tan atan asin acos abs re im conj floor ceil gamma erf zeta` | on numbers, exactly |
| `sec csc cot sinh cosh tanh asinh acosh atanh`, `arcsin arccos arctan log10 log2 factorial` | defined in the prelude |
| `simplify`, `together`, `coeff(p, x, k)`, `free(e, x)` | |
| `min max sort mean median variance pvariance stdev pstdev norm round arg` | lists of numbers, ordered exactly |
| `diff(f, x, y)`, `diff(f, x, 2, y)`, `integrate(f, [x, a, b])` | several variables; the list form of limits |
| `Si`, `zeta`, `factorial`, `fibonacci`, `lucas`, `bernoulli`, `partitions` | |

## Build
    make deps    # FLINT 3.3.1 and msolve 0.9.0, static, into deps/
    make         # amath (static, about 13 MB)
    make test

The engines are training wheels: see ENGINES.md for what each function uses now and the road to our own
implementations.

## License
To be decided (msolve is GPL-2.0-or-later and is linked statically).
