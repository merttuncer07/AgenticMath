#!/bin/sh
# Every statement in tests/cases.txt must give exactly the expected output.
cd "$(dirname "$0")/.." || exit 2
fail=0; n=0
while IFS= read -r line; do
  case "$line" in ''|'#'*) continue;; esac
  stmt=${line%% ||| *}; want=${line#* ||| }
  got=$(./amath -e "$stmt")
  n=$((n+1))
  if [ "$got" != "$want" ]; then echo "FAIL: $stmt"; echo "  want: $want"; echo "  got:  $got"; fail=$((fail+1)); fi
done < tests/cases.txt
# a program: definitions, rules with patterns and conditions, recursion, show
got=$(./amath tests/rules.am)
n=$((n+1))
[ "$got" = "$(cat tests/rules.out)" ] || { echo "FAIL: tests/rules.am"; echo "$got" | diff tests/rules.out - | head; fail=$((fail+1)); }
# -j: one JSON line with answer, status, verdict, facts
got=$(./amath -j -e 'factor(x^4 - 1)')
n=$((n+1))
[ "$got" = '{"input":"factor(x^4 - 1)","answer":"(x - 1)*(x + 1)*(x^2 + 1)","status":"proved","verdict":"every factor proved irreducible over Q (complete univariate factorization); multiplied back","facts":{"irreducible":false,"squarefree":true,"factor_degrees":[1,1,2],"multiplicities":[1,1,1],"rational_roots":["1","-1"]}}' ] || { echo "FAIL: -j factor: $got"; fail=$((fail+1)); }
# one portable file: runs from an empty directory
tmp=$(mktemp -d); cp amath "$tmp/"
got=$(cd "$tmp" && ./amath -e 'N(pi, 20)')
rm -rf "$tmp"
n=$((n+1))
[ "$got" = '3.1415926535897932385  [certified: digits guaranteed by ball arithmetic (Arb/Calcium)]' ] || { echo "FAIL: portable: $got"; fail=$((fail+1)); }
echo "run.sh: $n checks, $fail failed"
[ $fail -eq 0 ]
