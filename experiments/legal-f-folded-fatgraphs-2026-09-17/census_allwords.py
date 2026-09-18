"""Census of the word-free certificate LP over the automorphisms of phi_scan4.json.

For each automorphism and power m: enumerate admissible type polygons, solve the LP, and
  infeasible  -> verify an exact Farkas vector (no legal f^m-folded fatgraph at all)
  min chi = 0 -> verify an exact dual vector (every legal f^m-folded fatgraph has chi = 0)
  min chi < 0 -> report the candidate.
usage: python3 census_allwords.py m start stop out.log
"""
import sys, json, time
import numpy as np
import lp_allwords as LA

m, start, stop, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
data = json.load(open("phi_scan4.json"))[start:stop]
f = open(out, "a")
t0 = time.time()
stats = {}
for n, (_, lam, phi0, cp, gstr) in enumerate(data, start):
    phi = LA.power(phi0, m)
    g = LA.gates(phi)
    gp = len({g[x] for x in phi}); gn = len({g[x.upper()] for x in phi})
    maxval = max(2, 2 * min(gp, gn))
    TY = LA.Types(phi, g)
    polys = LA.polygons(TY, g, maxval)
    res, built = LA.solve(TY, polys)
    if res.status == 2:
        ok, den, _ = LA.farkas_infeasible(TY, polys, built)
        verdict = "infeasible-exact" if ok else "infeasible-float"
    elif res.status == 0 and res.fun > -1e-9:
        z = np.asarray(res.eqlin.marginals)
        ok, den = LA.exact_dual(TY, polys, built, z)
        if not ok:
            ok, den = LA.exact_dual(TY, polys, built, -z)
        verdict = "chi0-exact" if ok else "chi0-float"
    elif res.status == 0:
        verdict = "NEGATIVE %.6f" % res.fun
    else:
        verdict = "lp-status-%d" % res.status
    key = verdict.split()[0]
    stats[key] = stats.get(key, 0) + 1
    f.write("%d %s m=%d gates+%d gates-%d polys=%d %s\n" % (n, json.dumps(phi0), m, gp, gn, len(polys), verdict))
    f.flush()
f.write("stats m=%d [%d,%d) %s time %.1f\n" % (m, start, stop, json.dumps(stats), time.time() - t0))
f.close()
