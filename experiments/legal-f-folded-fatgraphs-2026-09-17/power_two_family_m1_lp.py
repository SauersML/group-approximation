"""Power-one word-free LP (as in census_allwords.py) for phi_k : a -> abb, b -> c a^k, c -> babb.

infeasible with an exact Farkas vector -> no legal f-folded fatgraph over this rose representative.
usage: python3 power_two_family_m1_lp.py KMIN KMAX out.log
"""
import sys, json, time
import numpy as np
import lp_allwords as LA

KMIN, KMAX, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
f = open(out, "a")
for k in range(KMIN, KMAX + 1):
    t0 = time.time()
    phi = {"a": "abb", "b": "c" + "a" * k, "c": "babb"}
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    TY = LA.Types(phi, g)
    polys = LA.polygons(TY, g, max(2, 2 * min(gp, gn)))
    res, built = LA.solve(TY, polys)
    if res.status == 2:
        ok, den, _ = LA.farkas_infeasible(TY, polys, built)
        verdict = "infeasible-exact" if ok else "infeasible-float"
    elif res.status == 0 and res.fun > -1e-9:
        verdict = "chi0"
    elif res.status == 0:
        verdict = "NEGATIVE %.6f" % res.fun
    else:
        verdict = "lp-status-%d" % res.status
    f.write("k=%d %s m=1 polys=%d %s time %.1f\n" % (k, json.dumps(phi), len(polys), verdict, time.time() - t0))
    f.flush()
f.close()
