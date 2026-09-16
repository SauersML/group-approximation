import sys, glob, collections
from fractions import Fraction
# usage: summarize.py OUTDIR FRONTIER WEIGHTFILE
outdir, frontier, wfile = sys.argv[1], sys.argv[2], sys.argv[3]
def nm(word):
    s = [1 if ch == "t" else -1 for ch in word if ch in "tT"]
    return len(s), sum(s)
lines = []
for f in sorted(glob.glob(outdir + "/out_p_*")):
    lines += open(f).read().splitlines()
front = open(frontier).read().splitlines()
# processed prefix must match the frontier order
proc = len(lines)
for a, b in zip(lines, front):
    pa, pb = a.split(), b.split()
    assert pa[0] == pb[0] and pa[1] == pb[1], (a, b)
tot = collections.Counter(); cert = collections.Counter(); minth = collections.Counter()
with open(wfile, "w") as out:
    for ln in lines:
        p = ln.split()
        k = nm(p[1]); tot[k] += 1
        if p[2] == "WEIGHT":
            cert[k] += 1
            th = [Fraction(x) for x in p[3].split("=", 1)[1].split(",")]
            minth[min(th)] += 1
            out.write(ln + "\n")
        else:
            assert p[2] == "FRONTIER", ln
fall = collections.Counter(nm(b.split()[1]) for b in front)
print("processed", proc, "of", len(front))
print("| n | m | frontier classes | processed | WEIGHT | remaining frontier |")
print("|---|---|---|---|---|---|")
for k in sorted(fall):
    print("| %d | %d | %d | %d | %d | %d |" % (k[0], k[1], fall[k], tot[k], cert[k], fall[k] - cert[k]))
print("| all | | %d | %d | %d | %d |" % (len(front), proc, sum(cert.values()), len(front) - sum(cert.values())))
print("min theta distribution", dict(sorted(minth.items())))
