# AgenticMath — notes for agents working on this repo

AgenticMath is a mathematics language whose first user is an AI agent; people should find it pleasant too.
Every answer gives an account of itself: the answer, how sure it is, facts the computation produced anyway, and
on request the steps actually taken.

## Principles
- The engines (FLINT with Arb and Calcium, msolve) are training wheels: use whatever gives the best answers now,
  keep their calls behind a small seam, and replace them one by one with our own implementations, each checked
  against the engine on random problems and benchmarked before the engine is removed. ENGINES.md is the ledger.
- One static binary that runs anywhere, installs nothing and writes nothing to disk.
- Small core. Measure on real problems against sympy (and others) before claiming anything is better.
- Status words mean exactly this: `proved` (a complete argument was carried out), `certified` (enclosed by
  rigorous interval/ball arithmetic), `exact` (computed with exact arithmetic), `numeric` (floating point, no
  guarantee), `unknown` (the engine could not decide). Never upgrade a status; a randomized result is never
  `proved`.
- Facts are only what the computation produced anyway: no extra computation to explain. Work lines are steps
  actually taken. Failures say why and what would be needed.
- Notation agents already write: `x^2` and `x**2`, `2x`, `sqrt`, `pi`, lists `[a, b]`, `f(x) = ...` equations.

## Practice
- C11; code, comments, commits and docs in English.
- `make deps` builds the engines into `deps/` (static); `make` builds `amath`; `make test` runs every check
  (keep it under 60 s).
- Each new function: implementation, a test with an independently checked answer, an entry in README.
