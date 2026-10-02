# AgenticMath

A mathematics language whose first user is an AI agent. One static binary, `amath`: nothing to install, nothing
written to disk. Every answer gives an account of itself.

    $ amath -e 'factor(x^4 - 1)'
    (x - 1)*(x + 1)*(x^2 + 1)  [proved: every factor proved irreducible over Q (complete univariate factorization); multiplied back]

    $ amath -j -e 'factor(x^4 - 1)'
    {"input":"factor(x^4 - 1)","answer":"(x - 1)*(x + 1)*(x^2 + 1)","status":"proved","verdict":"...",
     "facts":{"irreducible":false,"squarefree":true,"factor_degrees":[1,1,2],"multiplicities":[1,1,1],"rational_roots":["1","-1"]}}

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

## Functions (v0.1)
| | |
|---|---|
| arithmetic | exact rationals, algebraic numbers, pi, E, I; rational functions in up to 32 variables |
| `factor(n)`, `factor(p)` | whole numbers and fractions (primes proved); polynomials in one or many variables |
| `roots(p)`, `realroots(p)` | every root as an exact algebraic number (`sqrt(2)`, `RootOf(x^3 - x - 1, 1.32472)`) |
| `solve(eq, x)`, `solve([eqs], [vars])` | one equation exactly; polynomial systems via msolve, each solution exact and checked by substitution |
| `N(x, digits)` | decimals with every digit guaranteed |
| `diff`, `gcd`, `resultant`, `discriminant`, `degree`, `subs`, `numer`, `denom`, `binomial`, `isprime` | |
| `sqrt exp log sin cos tan atan asin acos abs re im conj floor ceil gamma` | on numbers, exactly |

## Build
    make deps    # FLINT 3.3.1 and msolve 0.9.0, static, into deps/
    make         # amath (static, about 13 MB)
    make test

The engines are training wheels: see ENGINES.md for what each function uses now and the road to our own
implementations.

## License
To be decided (msolve is GPL-2.0-or-later and is linked statically).
