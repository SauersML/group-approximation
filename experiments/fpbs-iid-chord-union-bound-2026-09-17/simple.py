"""Vertex-simple labelled chains K = x_0 -> ... -> x_n = Kb (all x_i distinct).

The union bound only needs self-avoiding paths in the class graph: if
class K and class Kb are joined, they are joined by a vertex-simple path.
R_s(h_1..h_n) counts such chains; each chain is one choice of points
y_i in x_{i-1} with x_i = class(h_i y_i).  Meet in the middle on full paths.
Usage: simple.py M n L [L2]   (all signed label sequences, labels |h| <= M).
"""
import sys, itertools
from chains import cls, rep, k_elements, reduced_words, in_K, inv


def paths(start, labels, KL):
    """all vertex-simple class paths from start following labels."""
    out = [(start,)]
    for h in labels:
        new = []
        for p in out:
            g = rep(p[-1])
            seen = set(p)
            for k in KL:
                d = cls(h + k + g)
                if d not in seen:
                    new.append(p + (d,))
        out = new
    return out


def R_s(labels, KL, target='b'):
    n = len(labels)
    s = (n + 1) // 2
    F = paths(cls(''), labels[:s], KL)
    B = paths(cls(target), [inv(h) for h in reversed(labels[s:])], KL)
    by = {}
    for q in B:
        by.setdefault(q[-1], []).append(set(q[:-1]))
    tot = 0
    for p in F:
        sp = set(p[:-1])
        for sq in by.get(p[-1], ()):
            if not (sp & sq):
                tot += 1
    return tot


def labels_upto(M):
    lab, seen = [], set()
    for m in range(1, M + 1):
        for w in reduced_words(m):
            if in_K(w) or w in seen:
                continue
            seen.add(w); seen.add(inv(w)); lab.append(w)
    return lab + [inv(w) for w in lab]


if __name__ == '__main__':
    M, n = int(sys.argv[1]), int(sys.argv[2])
    Ls = [int(x) for x in sys.argv[3:]]
    KLs = [k_elements(L) for L in Ls]
    signed = labels_upto(M)
    mx, tot, unstable = (0, None), 0, 0
    for seq in itertools.product(signed, repeat=n):
        vals = [R_s(list(seq), KL) for KL in KLs]
        if len(set(vals)) > 1:
            unstable += 1
        r = vals[-1]
        tot += r
        if r > mx[0]:
            mx = (r, seq)
    print('M', M, 'n', n, 'L', Ls, 'signed labels', len(signed))
    print('max R_s', mx, 'unstable', unstable)
    print('mean R_s', tot / len(signed) ** n, 'sum', tot)
