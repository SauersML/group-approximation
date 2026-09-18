"""Calibration for rips-segev-support-method-threshold-is-exactly-q-gamma.

Steenbock's gluing: lines = vertices of Phi, a 4-bouquet covering given by
permutations s1..s4 (no fixed points, so Phi has no loops).  A backtrack-free
path of Gamma projects to a non-backtracking walk in Phi (Lemma B of the
few-line proof).  Between consecutive b-edges the path either continues in the
same b-run ("silent" transition: fwd x4 -> fwd x1, fwd x3 -> fwd x2, bwd x1 ->
bwd x4, bwd x2 -> bwd x3) or runs an a-syllable (a "hop") on the current line.

  gamma = 2 * min over closed non-backtracking walks of #hops   (cycle fp length)
  rep   = min (t - s) over walks whose hop lines l_s = l_t

Theorem A of the node says 2 * rep >= gamma.  The script computes both by 0-1 BFS
on directed edges and checks 2*rep >= gamma; it also reports whether equality
holds (a shortest cycle repeats its first hop line after gamma/2 hops, so
equality is expected), and girth(Phi) <= gamma <= 2 girth(Phi).
Phi is hill-climbed by random swaps towards girth >= T.
Usage: python3 hop_repeats.py [seed] [n] [trials] [T]
"""
import random, sys
from collections import deque

def make_phi(n, rng):
    perms = []
    for _ in range(4):
        while True:
            p = list(range(n)); rng.shuffle(p)
            if all(p[i] != i for i in range(n)):
                break
        perms.append(p)
    return perms

def dedges(n, perms):
    # directed edge = (j, d, src, dst); d=+1 forward, -1 backward
    out = {v: [] for v in range(n)}
    inv = [[0] * n for _ in range(4)]
    for j in range(4):
        for v in range(n):
            inv[j][perms[j][v]] = v
    for j in range(4):
        for v in range(n):
            out[v].append((j, 1, v, perms[j][v]))
            out[v].append((j, -1, v, inv[j][v]))
    return out

SILENT = {((3, 1), (0, 1)), ((2, 1), (1, 1)), ((0, -1), (3, -1)), ((1, -1), (2, -1))}

def nb(e, f):
    return not (e[0] == f[0] and e[1] == -f[1] and e[3] == f[2] and e[2] == f[3])

def trans(e, f):
    return 0 if ((e[0], e[1]), (f[0], f[1])) in SILENT else 1

def bfs01(out, start, weight_start):
    """0-1 BFS over directed edges; dist[e] = hops from start edge to e."""
    dist = {start: weight_start}
    dq = deque([start])
    while dq:
        e = dq.popleft()
        for f in out[e[3]]:
            if not nb(e, f):
                continue
            w = trans(e, f)
            nd = dist[e] + w
            if f not in dist or nd < dist[f]:
                dist[f] = nd
                (dq.appendleft if w == 0 else dq.append)(f)
    return dist

def girth(n, out):
    best = 10 ** 9
    for s in range(n):
        # BFS on non-backtracking walks from s
        seen = {}
        dq = deque()
        for f in out[s]:
            dq.append((f, 1))
        while dq:
            e, d = dq.popleft()
            if d >= best:
                continue
            if e[3] == s:
                best = min(best, d)
                continue
            key = e
            if key in seen and seen[key] <= d:
                continue
            seen[key] = d
            for f in out[e[3]]:
                if nb(e, f):
                    dq.append((f, d + 1))
    return best

def short_closed(n, perms, T):
    """number of closed non-backtracking walks of length < T (all starts)."""
    out = dedges(n, perms)
    alle = [e for v in out for e in out[v]]
    tot = 0
    for e0 in alle:
        cur = {e0: 1}
        for L in range(1, T - 1):
            nxt = {}
            for e, c in cur.items():
                for f in out[e[3]]:
                    if nb(e, f):
                        nxt[f] = nxt.get(f, 0) + c
            cur = nxt
            tot += sum(c for e, c in cur.items() if e[3] == e0[2] and nb(e, e0))
        tot += (e0[3] == e0[2])
    return tot

def make_phi_girth(n, rng, T):
    perms = make_phi(n, rng)
    bad = short_closed(n, perms, T)
    steps = 0
    while bad > 0 and steps < 3000:
        steps += 1
        j = rng.randrange(4); v, w = rng.sample(range(n), 2)
        p = perms[j]
        p[v], p[w] = p[w], p[v]
        if p[v] == v or p[w] == w:
            p[v], p[w] = p[w], p[v]; continue
        nb_ = short_closed(n, perms, T)
        if nb_ <= bad:
            bad = nb_
        else:
            p[v], p[w] = p[w], p[v]
    return perms

def run(n, rng, T):
    perms = make_phi_girth(n, rng, T)
    out = dedges(n, perms)
    alle = [e for v in out for e in out[v]]
    # gamma: min cyclic #hops over closed nb walks.  Fix first edge e0; walk to an
    # edge e with nb(e, e0); cycle weight = dist[e] + trans(e, e0).
    minL = 10 ** 9
    for e0 in alle:
        dist = bfs01(out, e0, 0)
        for e, d in dist.items():
            if e[3] == e0[2] and nb(e, e0):
                minL = min(minL, d + trans(e, e0))
    gamma = 2 * minL
    # rep: start at a hop on line l: arriving edge a (dst l) then leaving f with
    # trans(a, f) = 1 and nb(a, f).  Count hops until again a hop on line l.
    rep = 10 ** 9
    for a in alle:
        l = a[3]
        for f in out[l]:
            if not nb(a, f) or trans(a, f) != 1:
                continue
            dist = bfs01(out, f, 0)
            for e, d in dist.items():
                if e[3] != l:
                    continue
                for h in out[l]:
                    if nb(e, h) and trans(e, h) == 1:
                        rep = min(rep, d + 1)   # the hop at l after e is hop number d+1
    g = girth(n, out)
    return g, gamma, rep

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    T = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    rng = random.Random(seed)
    viol = eq = 0
    for t in range(trials):
        g, gamma, rep = run(n, rng, T)
        assert g <= gamma <= 2 * g, (g, gamma)
        ok = 2 * rep >= gamma
        viol += not ok
        eq += (2 * rep == gamma)
        print("trial %2d n=%d girth(Phi)=%d gamma=%d min hop-repeat distance=%d  2*rep>=gamma: %s" % (t, n, g, gamma, rep, ok))
    print("seed %d: %d trials, %d violations of 2*rep >= gamma, equality in %d" % (seed, trials, viol, eq))
