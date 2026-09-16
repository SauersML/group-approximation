"""Search for counterexamples to the LOCAL claim in case 2 of the proof of Zaremsky 2410.11993 Thm 3.1.

Local problem (LP): finite integer metric space W, subset U of W, integers r < t.
Hypothesis: for every T subset of W with diam T <= t (T empty allowed),
  Y_T = {y in U : d(y,x) <= r for all x in T} is nonempty, and some c in Y_T has d(c,y) <= t for all y in Y_T.
Claim under test: VR_t(W) is contractible (we test reduced GF(2) homology).

An instance embeds into case 2 of the proof by adding a,b with d(a,b)=t, d(a,y)=d(b,y)=r (y in U),
d(a,w)=d(b,w)=t (w not in U), provided r=t-1 and d(y,y')<=2r, d(w,w')<=2t, d(y,w)<=t+r.
Then dclk({a,b}) = sd VR_t(W).  Usage: python3 local_lp_search.py n t iters seed
"""
import sys, random


def floyd(D, n):
    for k in range(n):
        Dk = D[k]
        for i in range(n):
            Di = D[i]
            dik = Di[k]
            for j in range(n):
                v = dik + Dk[j]
                if v < Di[j]:
                    Di[j] = v
    return D


def cliques(adj, n):
    # all cliques (including empty) as bitmasks
    out = [0]
    def rec(cur, cand):
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            nc = cur | (1 << v)
            out.append(nc)
            rec(nc, c & adj[v])
    rec(0, (1 << n) - 1)
    return out


def rank_gf2(rows):
    rank = 0
    pivots = {}
    for row in rows:
        x = row
        while x:
            p = x.bit_length() - 1
            if p in pivots:
                x ^= pivots[p]
            else:
                pivots[p] = x
                rank += 1
                break
    return rank


def reduced_betti(cl, n):
    bydim = {}
    for c in cl:
        if c == 0:
            continue
        d = bin(c).count('1') - 1
        bydim.setdefault(d, []).append(c)
    maxd = max(bydim) if bydim else -1
    index = {d: {c: i for i, c in enumerate(bydim[d])} for d in bydim}
    ranks = {}
    for d in range(1, maxd + 1):
        rows = []
        idx = index[d - 1]
        for c in bydim[d]:
            row = 0
            x = c
            while x:
                v = (x & -x)
                x &= x - 1
                row |= 1 << idx[c ^ v]
            rows.append(row)
        ranks[d] = rank_gf2(rows)
    betti = []
    for d in range(0, maxd + 1):
        nd = len(bydim[d])
        rk_out = ranks.get(d, 0)  # rank of boundary from dim d
        rk_in = ranks.get(d + 1, 0)
        b = nd - rk_out - rk_in
        if d == 0:
            b -= 1  # reduced
        betti.append(b)
    return betti


def check(D, n, U, t, r):
    adjt = [0] * n
    Br = [0] * n
    for i in range(n):
        for j in range(n):
            if D[i][j] <= t:
                adjt[i] |= 1 << j
            if D[i][j] <= r:
                Br[i] |= 1 << j
    adj = [adjt[i] & ~(1 << i) for i in range(n)]
    cl = cliques(adj, n)
    viol = 0
    for T in cl:
        Y = U
        x = T
        while x:
            v = (x & -x).bit_length() - 1
            x &= x - 1
            Y &= Br[v]
        if Y == 0:
            viol += 1
            continue
        ok = False
        y = Y
        while y:
            c = (y & -y).bit_length() - 1
            y &= y - 1
            if Y & ~adjt[c] == 0:
                ok = True
                break
        if not ok:
            viol += 1
    return viol, cl


def embeddable(D, n, U, t, r):
    if r != t - 1:
        return False
    for i in range(n):
        for j in range(n):
            ui = (U >> i) & 1
            uj = (U >> j) & 1
            lim = 2 * r if (ui and uj) else (2 * t if (not ui and not uj) else t + r)
            if D[i][j] > lim:
                return False
    return True


def main():
    n = int(sys.argv[1]); t = int(sys.argv[2]); iters = int(sys.argv[3]); seed = int(sys.argv[4])
    r = t - 1
    rng = random.Random(seed)
    M = 2 * r + 1
    found = 0
    valid = 0
    for it in range(iters):
        D = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                D[i][j] = D[j][i] = rng.randint(1, M)
        floyd(D, n)
        U = rng.randrange(1, 1 << n)
        viol, cl = check(D, n, U, t, r)
        # greedy repair: try flipping U bits / adjusting entries to reduce violations
        steps = 0
        while viol > 0 and steps < 60:
            steps += 1
            cand = []
            for b in range(n):
                cand.append(('U', b))
            for _ in range(12):
                i, j = rng.sample(range(n), 2)
                cand.append(('D', i, j, rng.randint(1, M)))
            best = None
            for c in cand:
                if c[0] == 'U':
                    U2 = U ^ (1 << c[1])
                    if U2 == 0:
                        continue
                    D2 = D
                else:
                    U2 = U
                    D2 = [row[:] for row in D]
                    D2[c[1]][c[2]] = D2[c[2]][c[1]] = c[3]
                    floyd(D2, n)
                v2, cl2 = check(D2, n, U2, t, r)
                if best is None or v2 < best[0]:
                    best = (v2, D2, U2, cl2)
            if best[0] <= viol:
                viol, D, U, cl = best
            else:
                break
        if viol > 0:
            continue
        valid += 1
        betti = reduced_betti(cl, n)
        if any(betti):
            found += 1
            print('COUNTEREXAMPLE n', n, 't', t, 'r', r, 'U', bin(U), 'betti', betti,
                  'embeddable', embeddable(D, n, U, t, r), flush=True)
            for row in D:
                print(' ', row, flush=True)
            if found >= 3:
                break
    print('iters', iters, 'valid', valid, 'found', found, flush=True)


if __name__ == '__main__':
    main()
