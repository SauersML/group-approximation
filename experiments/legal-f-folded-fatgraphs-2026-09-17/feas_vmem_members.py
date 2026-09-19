"""Second check of feas_vmem_exact.py's polygon test: each polygon of a saved rational point is found by the
enumeration of farkas_vmem_brute.walk (run from the polygon's smallest type only).
  python3 feas_vmem_members.py point.json"""
import sys, json
import lp_vmem as VM
import farkas_vmem_brute_shard as BS

J = json.load(open(sys.argv[1]))
phi, g, TY, maxval = VM.setup(J["phi0"], J["power"], J["rm"], J["rp"])
polys = [tuple((int(d), int(q)) for d, q in P) for P in J["polys"]]
def canon(P):
    k = min(range(len(P)), key=lambda i: P[i][0]); return tuple(P[k:] + P[:k])
want = {canon(P) for P in polys}
found = set()
starts = sorted({P[0][0] for P in want})
for d1 in starts:                      # walk_shard with K = N and i = d1 enumerates exactly the polygons with min type d1
    BS.walk_shard(TY, g, maxval, lambda sl: found.add(tuple(sl)) if tuple(sl) in want else None, TY.N, d1)
print("polygons", len(want), "found by the brute enumeration", len(want & found), "start types", len(starts))
print("MEMBERSHIP", "VERIFIED" if want <= found else "FAILED")
