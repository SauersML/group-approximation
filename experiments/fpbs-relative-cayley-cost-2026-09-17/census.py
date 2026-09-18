"""Census: for cyclically reduced v in F(c,d), not a proper power, using both
letters, compute rank(H_s cap g H_s g^-1) for H_s = <s, v>, g in {t, t^-1},
{s,t} = {c,d}.

Positive rank => the t-edges between H_s-classes come in infinite contact sets
=> letter-saturated contact repair gives RC(v) = 1.
Rank 0 for both s and both g => every such repair must keep all t-edges.
A one-vertex Stallings graph for H_s means H_s = F_2 (v primitive, completing s).
"""
import itertools
import sys
from stallings import fold, subgroup_rank_intersection, inv, INV

L = ['c', 'C', 'd', 'D']


def reduced(w):
    return all(INV[w[i]] != w[i + 1] for i in range(len(w) - 1))


def cyc_reduced(w):
    return reduced(w) and INV[w[0]] != w[-1]


def proper_power(w):
    n = len(w)
    return any(n % k == 0 and w[:k] * (n // k) == w for k in range(1, n))


def canon(w):
    iw = inv(w)
    rots = [w[i:] + w[:i] for i in range(len(w))]
    rots += [iw[i:] + iw[:i] for i in range(len(iw))]
    return min(rots)


def analyse(w):
    ff = False
    hits = []
    for s, t in (('c', 'd'), ('d', 'c')):
        H = [s, w]
        G, b = fold(H)
        if G.n == 1:
            ff = True
        for g in (t, INV[t]):
            r = subgroup_rank_intersection(H, [g + h + inv(g) for h in H])
            hits.append((s, g, r))
    return ff, hits


def main(maxlen):
    seen = set()
    stats = {'total': 0, 'free_factor': 0, 'contact': 0, 'none': 0}
    ex_c, ex_n = [], []
    for n in range(2, maxlen + 1):
        for tup in itertools.product(L, repeat=n):
            w = ''.join(tup)
            if not cyc_reduced(w) or proper_power(w):
                continue
            if not (set(w) & {'c', 'C'}) or not (set(w) & {'d', 'D'}):
                continue
            cw = canon(w)
            if cw in seen:
                continue
            seen.add(cw)
            stats['total'] += 1
            ff, hits = analyse(w)
            pos = [h for h in hits if h[2] > 0]
            if ff:
                stats['free_factor'] += 1
            elif pos:
                stats['contact'] += 1
                ex_c.append((w, pos))
            else:
                stats['none'] += 1
                ex_n.append(w)
    print(stats)
    print('contact examples:', ex_c[:20])
    print('no-contact examples:', ex_n[:20])


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
