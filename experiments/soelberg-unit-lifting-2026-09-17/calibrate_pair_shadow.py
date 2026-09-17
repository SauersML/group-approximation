#!/usr/bin/env python3
"""Calibration for pair_shadow_classification.py: every trivial unit +-g of Q[S] on the pair (g in A,
g^{-1} in B) satisfies all equations of the matching shadow case (localization equation removed), checked
by exact evaluation; and a perturbed point does not."""
import sympy
from soelberg_engine import A, B, minv
from pair_shadow_classification import system, SA, N

def evaluate(polys, vals):
    syms = {v: sympy.Symbol(v) for v in vals}
    bad = 0
    for p in polys:
        e = sympy.sympify(p, locals=syms)
        if e.subs(vals) != 0:
            bad += 1
    return bad

ok = tried = 0
for k in range(N):
    g = A[k]
    if minv(g) not in B:
        continue
    l = B.index(minv(g))
    m1, c1 = SA[1][k]
    m2, c2 = SA[2][k]
    # U = c1 A_k so rho1(U) = m1 ; V = c1 B_l ; rho2(U) = c1 c2 m2 -> lam = c1 c2
    vals = {'u%d' % (q + 1): 0 for q in range(N)}
    vals.update({'v%d' % (q + 1): 0 for q in range(N)})
    vals['u%d' % (k + 1)] = c1
    vals['v%d' % (l + 1)] = c1
    vals['lam'] = c1 * c2
    vals['mu'] = c1 * c2

    vs, ps = system(m1, m2, -1, 0)    # zero = {} (no localization zeros)
    ps = ps[:-1]                      # drop the localization equation
    bad = evaluate(ps, vals)
    vals['u%d' % (k + 1)] = c1 + 1    # perturbation
    bad_pert = evaluate(ps, vals)
    tried += 1
    ok += (bad == 0 and bad_pert > 0)
    print('trivial unit A_%d: violated equations %d (perturbed: %d)' % (k + 1, bad, bad_pert))
print('calibration: %d of %d trivial units satisfy their shadow case exactly and fail when perturbed' % (ok, tried))

# Part 2: msolve pipeline calibration.  For each trivial unit A_k of the pair, the shadow case of A_k with
# the localization replaced by "u_m = 0 for m != k, w u_k = 1" must be solvable (output not [-1]), and the
# same system with the wrong monomial m1 (a different rho1 class) must be [-1].
import subprocess, os, tempfile
from pair_shadow_classification import classes
M1 = sorted(classes(SA[1]))
def run(vs, ps):
    with tempfile.TemporaryDirectory() as d:
        fi, fo = os.path.join(d, 'in.ms'), os.path.join(d, 'out.ms')
        open(fi, 'w').write(','.join(vs) + '\n0\n' + ',\n'.join(ps) + '\n')
        subprocess.run(['msolve', '-t', '1', '-f', fi, '-o', fo], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return open(fo).read().strip()
good = 0
for k in range(N):
    if minv(A[k]) not in B:
        continue
    m1, _ = SA[1][k]; m2, _ = SA[2][k]
    vs, ps = system(m1, m2, -1, 0)
    ps = ps[:-1] + ['u%d' % (q + 1) for q in range(N) if q != k] + ['w*u%d-1' % (k + 1)]
    out_right = run(vs, ps)
    wrong = [m for m in M1 if m != m1][0]
    vs2, ps2 = system(wrong, m2, -1, 0)
    ps2 = ps2[:-1] + ['u%d' % (q + 1) for q in range(N) if q != k] + ['w*u%d-1' % (k + 1)]
    out_wrong = run(vs2, ps2)
    r_ok = not out_right.startswith('[-1]')
    w_ok = out_wrong.startswith('[-1]')
    good += r_ok and w_ok
    print('msolve calibration A_%d: correct case solvable %s (%s...), wrong monomial inconsistent %s' % (
        k + 1, r_ok, out_right[:40].replace('\n', ' '), w_ok))
print('msolve pipeline calibration: %d of 21 trivial units behave as expected' % good)
