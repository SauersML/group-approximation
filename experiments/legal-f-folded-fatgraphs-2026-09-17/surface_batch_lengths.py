"""Turn LP-negative census entries into verified surface-subgroup certificates.

For every line of a census log with verdict NEGATIVE, try d^- boundaries {w, w^-1} for the
cyclically legal words w whose lengths are listed in the environment variable LENS
(comma separated, default 4; surface_batch.py is the case LENS=2,3), searching an f^m-folded legal
fatgraph with sat4.solve4, re-checking with sat4.verify4 (including the X_n unrolling for
n <= 2), and finally with the independent checker verify_surface.py. Certificates are written to
OUTDIR/phi<n>.json.

usage: LENS=4 python3 surface_batch_lengths.py census.log m OUTDIR out.log
"""
import sys, json, os, subprocess, itertools
from ffold import Boundary, gate_of, cyc_legal
from search3 import power
from sat4 import solve4, verify4, orbits

log, m, outdir, out = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
os.makedirs(outdir, exist_ok=True)
done = set()
if os.path.exists(out):
    for line in open(out):
        done.add(int(line.split()[0]))
f = open(out, "a")
for line in open(log):
    if "NEGATIVE" not in line or line.startswith("stats") or line.startswith("chunk"):
        continue
    n = int(line.split()[0])
    if n in done:
        continue
    phi0 = json.loads(line[line.index("{"):line.index("}") + 1])
    phi = power(phi0, m)
    g = gate_of(phi)
    iw = lambda w: w[::-1].swapcase()
    found = None
    for L in tuple(int(x) for x in os.environ.get("LENS","4").split(",")):
        for t in itertools.product("abcABC", repeat=L):
            w = "".join(t)
            if any(w[i] == iw(w[(i + 1) % L]) for i in range(L)) or not cyc_legal(g, w):
                continue
            B = Boundary(phi, [w, iw(w)])
            p, it = solve4(B, g, maxiter=2000)
            if not p:
                continue
            rep = verify4(B, p, g, nunroll=2)
            vs = orbits(B, p)
            path = os.path.join(outdir, "phi%d.json" % n)
            json.dump({"phi0": phi0, "power": m, "phi": phi, "minus_words": [w, iw(w)],
                       "boundary": B.words, "labels": B.label, "kind": B.kind, "fdart": B.fdart,
                       "nxt": B.nxt, "pairing": [p[d] for d in range(B.N)],
                       "vertices": [[(d, B.label[d]) for d in o] for o in vs], "report": rep},
                      open(path, "w"), indent=1)
            r = subprocess.run(["python3", "verify_surface.py", path], capture_output=True, text=True)
            ok = r.returncode == 0
            found = "SURFACE w=%s chi=%d independent=%s %s" % (w, rep["chi"], ok,
                                                             r.stdout.strip() if ok else r.stderr.strip().splitlines()[-1])
            if ok:
                break
        if found and "independent=True" in found:
            break
    f.write("%d %s m=%d %s\n" % (n, json.dumps(phi0), m, found or "no-certificate-with-length-in-" + os.environ.get("LENS","4")))
    f.flush()
f.close()
