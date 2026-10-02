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
# lean: Lean 4 proofs in the facts
for pair in 'lean cofactors(x^3 + y^3 = 0, [x + y = 0])|linear_combination (x^2 - x*y + y^2) * h1' \
            'lean factor(x^4 - 1)|example (x : ℚ) : x^4 - 1 = (x - 1)*(x + 1)*(x^2 + 1) := by ring' \
            'lean (a-b)*(a+b) == a^2 - b^2|example (a b : ℚ) : ((a - b) * (a + b)) = ((a ^ 2) - (b ^ 2)) := by ring' \
            'lean isprime(1000003)|example : Nat.Prime 1000003 := by norm_num'; do
  stmt=${pair%%|*}; want=${pair#*|}
  got=$(./amath -j -e "$stmt")
  n=$((n+1))
  case "$got" in *"$want"*) ;; *) echo "FAIL: $stmt: $got"; fail=$((fail+1));; esac
done
# --mcp: initialize, list the tools, evaluate in a session that keeps definitions
got=$(printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18"}}' \
  '{"jsonrpc":"2.0","method":"notifications/initialized"}' '{"jsonrpc":"2.0","id":2,"method":"tools/list"}' \
  '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"evaluate","arguments":{"code":"f(x) := x^2 + 1\nfactor(f(x)^2 - 4)"}}}' \
  '{"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"evaluate","arguments":{"code":"factr(12)"}}}' | ./amath --mcp)
for want in '"id":1,"result":{"protocolVersion":"2025-06-18"' '"name":"evaluate"' '"name":"reference"' \
            '(x - 1)*(x + 1)*(x^2 + 3)' '\"did_you_mean\":\"factor\"'; do
  n=$((n+1))
  case "$got" in *"$want"*) ;; *) echo "FAIL: mcp: missing $want"; fail=$((fail+1));; esac
done
n=$((n+1))
[ "$(printf "%s\n" "$got" | wc -l)" -eq 4 ] || { echo "FAIL: mcp: expected 4 replies (none to the notification)"; fail=$((fail+1)); }
# one portable file: runs from an empty directory
tmp=$(mktemp -d); cp amath "$tmp/"
got=$(cd "$tmp" && ./amath -e 'N(pi, 20)')
rm -rf "$tmp"
n=$((n+1))
[ "$got" = '3.1415926535897932385  [certified: digits guaranteed by ball arithmetic (Arb/Calcium)]' ] || { echo "FAIL: portable: $got"; fail=$((fail+1)); }
echo "run.sh: $n checks, $fail failed"
[ $fail -eq 0 ]
