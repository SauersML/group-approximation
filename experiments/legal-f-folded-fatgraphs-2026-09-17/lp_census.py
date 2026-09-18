"""Run lp5 over many automorphisms (and control endomorphisms) with short words.
usage: python3 lp_census.py census.json nphi m maxlen maxdarts tlimit_per_phi"""
import sys, json, time, random
from ffold import *
from search3 import power
from search2 import legal_words_dfs
from lp5 import run_word

def scan(phi0, m, maxlen, maxdarts, tl):
    phi = power(phi0, m); g = gate_of(phi)
    gp = len({g[d] for d in "abc"}); gn = len({g[d] for d in "ABC"})
    if min(gp, gn) <= 1: return "min-gates<=1", 0, None
    words = sorted(legal_words_dfs(g, maxlen, True), key=lambda w: (len(w), w))
    words = [w for w in words if len(w) + len(apply(phi, w)) <= maxdarts]
    t0 = time.time(); n = 0
    for w in words:
        chi, B, polys, res = run_word(phi, g, w, 2 * min(gp, gn))
        n += 1
        if chi is not None and chi < -1e-9: return "NEGATIVE", n, (w, chi)
        if chi is not None: return "chi0", n, w
        if time.time() - t0 > tl: break
    return "all infeasible", n, None

if __name__ == "__main__":
    data = json.load(open(sys.argv[1])); nphi = int(sys.argv[2])
    m, maxlen, maxdarts, tl = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6])
    random.seed(1); sample = random.sample(data, nphi) if nphi < len(data) else data
    for r in sample:
        phi0 = r[2]
        print(phi0, r[4], *scan(phi0, m, maxlen, maxdarts, tl), flush=True)
