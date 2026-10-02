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
