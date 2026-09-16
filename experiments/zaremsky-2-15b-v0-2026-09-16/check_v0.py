"""Sanity check of the record-time construction in
research/artifacts/infinite-order-v-elements-hyperbolic-points-2026-09-16.md (Lemma 2).
Random elements g of V (random complete prefix codes, random bijection). Follow a long
finite word under g (or g^{-1}), started after 1500 steps of the inverse; whenever the drift s_k exceeds D(2^N-1), locate two
records with equal N-prefix, pull back, and verify h = g^{m'-m} maps w r y -> w y.
Evidence only; the proof is in the artifact."""
import random, sys

def code(n, rng):
    leaves = ['']
    while len(leaves) < n:
        l = leaves.pop(rng.randrange(len(leaves)))
        leaves += [l + '0', l + '1']
    return leaves

def apply(pairs, w):
    for u, v in pairs:
        if w.startswith(u):
            return v + w[len(u):]
    return None  # word too short to decide

def run(seed, trials=400):
    rng = random.Random(seed)
    stats = dict(lemma2_cases=0, verified=0, failures=0)
    for _ in range(trials):
        n = rng.randrange(2, 6)
        U, W = code(n, rng), code(n, rng)
        rng.shuffle(W)
        g = list(zip(U, W)); gi = [(v, u) for u, v in g]
        N = max(max(len(u), len(v)) for u, v in g)
        D = max(abs(len(u) - len(v)) for u, v in g)
        for f, finv in ((g, gi), (gi, g)):
            x0 = ''.join(rng.choice('01') for _ in range(200))
            for _ in range(1500):  # push toward a repeller of f (attractor of finv)
                x0 = apply(finv, x0) if len(x0) >= N else x0
            xs = [x0]
            while len(xs) < 3000 and len(xs[-1]) >= N:
                xs.append(apply(f, xs[-1]))
            s = [len(xs[0]) - len(x) for x in xs]
            K = D * (2 ** N - 1)
            ks = [k for k in range(len(s)) if s[k] > K]
            if D == 0 or not ks:
                continue
            k = ks[0]
            stats['lemma2_cases'] += 1
            recs, best = [], None
            for m in range(k + 1):
                if best is None or s[m] > best:
                    recs.append(m); best = s[m]
            assert len(recs) >= 2 ** N + 1, (len(recs), N)
            seen, pair = {}, None
            for m in recs:
                key = xs[m][:N]
                if key in seen:
                    pair = (seen[key], m); break
                seen[key] = m
            m0, m1 = pair
            w = xs[m1][:N]; c = w
            for _ in range(m1 - m0):
                c = apply(finv, c)
            ok = (c is not None and xs[m0].startswith(c)
                  and len(c) == N + s[m1] - s[m0] and c.startswith(w) and len(c) > N)
            r = c[N:] if ok else ''
            for _ in range(5):
                y = ''.join(rng.choice('01') for _ in range(60))
                z = w + r + y
                for _ in range(m1 - m0):
                    z = apply(f, z)
                ok = ok and z is not None and z == w + y
            stats['verified' if ok else 'failures'] += 1
    return stats

if __name__ == '__main__':
    print(run(int(sys.argv[1]) if len(sys.argv) > 1 else 1))
