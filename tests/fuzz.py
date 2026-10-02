"""Random and malformed statements: amath must answer every one (an answer or an error), never crash or hang.
    python3 tests/fuzz.py [seed] [count]"""
import random, subprocess, sys

ATOMS = ['x', 'y', 'k', 'a', '0', '1', '2', '-1', '1/2', '0.5', 'pi', 'E', 'I', 'oo', 'sqrt(2)', '3', '10^30']
FUNCS = ['sin', 'cos', 'tan', 'exp', 'log', 'sqrt', 'atan', 'factor', 'roots', 'diff', 'integrate', 'series', 'limit',
         'N', 'det', 'inverse', 'sum', 'subs', 'solve', 'simplify', 'gcd', 'mod', 'divisors', 'eigenvals', 'abs',
         'taylor', 'linsolve', 'cofactors', 'isprime', 'nextprime', 'f', 'help']
OPS = ['+', '-', '*', '/', '^', '==', '=', '<']

def expr(d):
    r = random.random()
    if d <= 0 or r < 0.25: return random.choice(ATOMS)
    if r < 0.55: return '(' + expr(d - 1) + ' ' + random.choice(OPS) + ' ' + expr(d - 1) + ')'
    if r < 0.85:
        f = random.choice(FUNCS)
        n = random.choice([1, 1, 2, 2, 3, 4])
        return f + '(' + ', '.join(expr(d - 1) for _ in range(n)) + ')'
    if r < 0.95: return '[' + ', '.join(expr(d - 1) for _ in range(random.randint(0, 3))) + ']'
    return '-' + expr(d - 1)

def garble(s):
    s = list(s)
    for _ in range(random.randint(1, 3)):
        i = random.randrange(len(s) + 1)
        op = random.random()
        if op < 0.4 and s: del s[min(i, len(s) - 1)]
        else: s.insert(i, random.choice('()[],^*/+-=!"#@:;x1 '))
    return ''.join(s)

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
count = int(sys.argv[2]) if len(sys.argv) > 2 else 500
crashes, hangs = [], []
batch = []
for i in range(count):
    s = expr(random.randint(1, 4))
    if random.random() < 0.3: s = garble(s)
    batch.append(s.replace('\n', ' '))
for s in batch:
    try:
        p = subprocess.run(['./amath', '-e', s], capture_output=True, text=True, timeout=10)
        empty = not s.strip() or s.strip().startswith('#')
        if p.returncode not in (0, 1) or (not p.stdout.strip() and not empty):
            crashes.append((s, p.returncode, p.stderr[-200:]))
    except subprocess.TimeoutExpired:
        hangs.append(s)
for s, rc, err in crashes: print('CRASH', rc, repr(s), err.strip()[:120])
for s in hangs: print('HANG', repr(s))
print(f'{count} statements: {len(crashes)} crashes, {len(hangs)} hangs')
sys.exit(1 if crashes else 0)
