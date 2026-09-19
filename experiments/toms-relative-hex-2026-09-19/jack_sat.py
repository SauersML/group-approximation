"""Relative Hex on the jack: F(3) counterexamples whose level-2 set is the eight octants.

Let W be the union of the three midplanes x_nu = 1/2 of I^3 (the "jack").  Put level 2 on
the eight closed octants, shrunk away from W, and let R be a thin neighbourhood of W.  If a
usc level function with values {0, 1} on the cells of W has every level-1 component failing
two coordinates and every level-0 component failing one, then thickening it along the normal
fibres of W (the projection that sends indices n - 1, n + 1 to n is monotone for the face
order, has connected fibres and keeps the indices 0 and 2n) and adding the eight octant blobs
(each misses the three faces through its far corner) gives a genuine face counterexample to
F(3).  The octant blob is the grown normal form in which all eight corner types are present
and meet at the centre.

The model is face_form_sat.py restricted to the cells of W (cells with some index equal to
n, n even), with levels 0..maxlev on W.  Only maxlev = 1 is sound: with maxlev = 2 the
model drops the contact between level 2 on W and the octant blobs (which would merge them),
and it is trivially SAT (n = 4, 0 s), so that run carries no information.

Usage: python3 jack_sat.py n [maxlev]      (n even)
SAT at maxlev = 1 is a genuine counterexample to F(3).
"""
import sys, json
import face_form_sat as base


def keep(c, L):
    n = (L - 1) // 2
    return any(x == n for x in c)


if __name__ == '__main__':
    n = int(sys.argv[1])
    maxlev = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    assert n % 2 == 0
    ok, dt, sol = base.run(3, n, maxlev, keep=keep)
    print(json.dumps({'model': 'jack', 'N': 3, 'n': n, 'maxlev': maxlev,
                      'cells': (2 * n + 1) ** 3 - (2 * n) ** 3,
                      'result': 'SAT' if ok else 'UNSAT', 'seconds': round(dt, 2)}), flush=True)
    if ok:
        with open(f'sol_jack_n{n}_lev{maxlev}.json', 'w') as f:
            json.dump(sol, f)
