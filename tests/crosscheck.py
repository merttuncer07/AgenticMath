"""Cross-check amath against sympy on random problems. Not part of `make test` (it needs sympy):
    python3 tests/crosscheck.py [seed] [count]
Each answer is parsed back and compared with the question (factor), or compared numerically with sympy
(roots, systems, N)."""
import json, random, subprocess, sys, time

import sympy as sp
from sympy.parsing.sympy_parser import parse_expr, standard_transformations, convert_xor, implicit_multiplication_application

AMATH = './amath'
x, y, z = sp.symbols('x y z')
T = standard_transformations + (convert_xor, implicit_multiplication_application)


def amath(stmt):
    t = time.time()
    out = subprocess.run([AMATH, '-j', '-e', stmt], capture_output=True, text=True).stdout.strip()
    return json.loads(out), time.time() - t


def P(s):
    return parse_expr(s, transformations=T, local_dict={'x': x, 'y': y, 'z': z, 'I': sp.I, 'pi': sp.pi})


def amstr(e):
    return str(e).replace('**', '^')


def rand_poly(vars_, deg, coef=9):
    terms = [random.randint(-coef, coef) * sp.prod(v ** random.randint(0, deg) for v in vars_) for _ in range(random.randint(2, 4))]
    return sp.expand(sum(terms) + random.randint(1, 3) * vars_[0] ** deg)


def check_factor(rounds):
    bad = 0
    for _ in range(rounds):
        vars_ = [x] if random.random() < 0.6 else [x, y]
        f = sp.Integer(random.choice([1, 2, -3, sp.Rational(1, 2)]))
        for _ in range(random.randint(1, 3)):
            f *= rand_poly(vars_, random.randint(1, 4)) ** random.choice([1, 1, 2])
        f = sp.expand(f)
        if f.is_number:
            continue
        r, _ = amath(f'factor({amstr(f)})')
        if 'error' in r:
            print('ERROR', f, r['error']); bad += 1; continue
        back = P(r['answer'])
        ours = sum(e for _, e in sp.factor_list(back)[1])                 # irreducible pieces in our answer
        theirs = sum(e for _, e in sp.factor_list(f)[1])
        if sp.expand(back - f) != 0 or len(r['facts']['factor_degrees']) == 0 and theirs:
            print('BAD factor', f, '->', r['answer']); bad += 1
        elif sum(r['facts']['multiplicities']) != theirs:
            print('BAD count', f, '->', r['answer'], 'sympy', sp.factor_list(f)); bad += 1
    return bad


def check_roots(rounds):
    bad = 0
    for _ in range(rounds):
        f = sp.expand(sp.prod(rand_poly([x], random.randint(1, 3)) for _ in range(random.randint(1, 2))))
        if sp.degree(f, x) < 1:
            continue
        r, _ = amath(f'N(roots({amstr(f)}), 20)')
        if 'error' in r:
            print('ERROR', f, r['error']); bad += 1; continue
        ours = sorted((complex(P(s.strip())) for s in r['answer'][1:-1].split(',')), key=lambda c: (round(c.real, 8), round(c.imag, 8)))
        theirs = sorted((complex(v) for v in sp.Poly(sp.sqf_part(f), x).nroots(n=30, maxsteps=200)), key=lambda c: (round(c.real, 8), round(c.imag, 8)))
        distinct = []
        for v in theirs:
            if not any(abs(v - w) < 1e-8 for w in distinct):
                distinct.append(v)
        if len(ours) != len(distinct) or any(min(abs(o - t) for t in distinct) > 1e-10 for o in ours):
            print('BAD roots', f, ours, distinct); bad += 1
    return bad


def check_systems(rounds):
    bad = 0
    for _ in range(rounds):
        sols = [(random.randint(-4, 4), random.randint(-4, 4)) for _ in range(random.randint(1, 3))]
        # equations vanishing on chosen points, plus a random generic system
        if random.random() < 0.5:
            e1 = sp.expand(sp.prod(x - a for a, _ in sols)); e2 = sp.expand(y - sp.interpolate([(a, b) for a, b in sols], x)) if len({a for a, _ in sols}) == len(sols) else y - x
            eqs = [e1, e2]
        else:
            eqs = [rand_poly([x, y], 2, 5), rand_poly([x, y], 2, 5)]
        try:
            theirs = sp.solve(eqs, [x, y], dict=True)
        except Exception:
            continue
        r, _ = amath(f'N(solve([{", ".join(amstr(e) for e in eqs)}], [x, y]), 20)' if False else f'solve([{", ".join(amstr(e) for e in eqs)}], [x, y])')
        if 'error' in r:
            print('ERROR', eqs, r['error']); bad += 1; continue
        if r['answer'].startswith('infinitely'):
            continue
        n_ours = r['facts'].get('solutions', 0)
        n_theirs = len(theirs)
        if n_ours != n_theirs:
            print('BAD system count', eqs, n_ours, n_theirs); bad += 1
    return bad


def check_N(rounds):
    bad = 0
    exprs = ['pi', 'E', 'sqrt(2)', 'exp(pi)', 'log(3)', 'sin(1)', 'atan(1/3)', 'gamma(1/3)', 'sqrt(2)+sqrt(3)']
    for e in exprs[:rounds]:
        r, _ = amath(f'N({e}, 60)')
        theirs = sp.N(P(e), 80)
        if abs(sp.Float(r['answer'], 80) - theirs) > sp.Float(10) ** -58:
            print('BAD N', e, r['answer'], theirs); bad += 1
    return bad


if __name__ == '__main__':
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    res = {'factor': check_factor(n), 'roots': check_roots(n), 'systems': check_systems(n // 2), 'N': check_N(9)}
    print('failures:', res)
    sys.exit(1 if any(res.values()) else 0)
