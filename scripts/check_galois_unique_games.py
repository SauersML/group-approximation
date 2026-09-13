#!/usr/bin/env python3
# Brute-force replay of Galois-game Theorems 1, 2, 8, 10 on small permutation groups.
# val(Gal(G,K,mu)) = max over left transversals T of Pr_{t in T, s~mu}[s t in T].
import itertools, random, sys

def mul(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[i] for i in q)

def inv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)

def closure(gens, e):
    S = {e}
    frontier = [e]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(g, x)
                if y not in S:
                    S.add(y); new.append(y)
        frontier = new
    return frozenset(S)

def sym(n):
    return [tuple(p) for p in itertools.permutations(range(n))]

def subgroups(G, e, maxgens):
    subs = set()
    for r in range(0, maxgens + 1):
        for gens in itertools.combinations(G, r):
            subs.add(closure(gens, e))
    return subs

def classes(G):
    seen, out = set(), []
    for g in G:
        if g in seen: continue
        c = frozenset(mul(mul(x, g), inv(x)) for x in G)
        seen |= c; out.append(c)
    return out

def left_cosets(G, K):
    seen, out = set(), []
    for g in G:
        if g in seen: continue
        c = [mul(g, a) for a in sorted(K)]
        seen |= set(c); out.append(c)
    return out

def value(T, mu):
    Ts = set(T)
    return sum(w for t in T for s, w in mu.items() if mul(s, t) in Ts) / len(T)

def val_bruteforce(G, K, mu):
    cos = left_cosets(G, K)
    best = 0.0
    for choice in itertools.product(*cos):
        v = value(choice, mu)
        if v > best: best = v
    return best

def acts_freely(H, G, K):
    return all(len(H & frozenset(mul(mul(x, a), inv(x)) for a in K)) == 1 for x in G)

def main():
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    bad = 0; gapcases = []
    groups = {}
    S3 = sym(3); groups['S3'] = (S3, 2)
    S4 = sym(4); groups['S4'] = (S4, 2)
    e4 = tuple(range(4))
    D8 = sorted(closure([(1, 2, 3, 0), (0, 3, 2, 1)], e4)); groups['D8'] = (D8, 2)
    e8 = tuple(range(8))
    xor = lambda b: tuple(i ^ b for i in range(8))
    Z2c = sorted(closure([xor(1), xor(2), xor(4)], e8)); groups['Z2^3'] = (Z2c, 3)
    e6 = tuple(range(6))
    Z6 = sorted(closure([tuple((i + 1) % 6 for i in range(6))], e6)); groups['Z6'] = (Z6, 1)
    for name, (G, mg) in groups.items():
        e = tuple(range(len(G[0])))
        subs = subgroups(G, e, mg)
        cls = classes(G)
        for K in subs:
            if len(K) == 1 or len(K) == len(G): continue
            for trial in range(6):
                # symmetric conjugation-invariant mu, random support
                w = {c: (random.random() if random.random() < 0.7 else 0.0) for c in cls}
                tot = sum(w[c] * len(c) for c in cls)
                if tot == 0: continue
                mu0 = {g: w[c] / tot for c in cls for g in c if w[c] > 0}
                mu = {}
                for g, x in mu0.items():  # symmetrize: mu(g) = mu(g^-1)
                    mu[g] = mu.get(g, 0.0) + x / 2
                    mu[inv(g)] = mu.get(inv(g), 0.0) + x / 2
                v = val_bruteforce(G, K, mu)
                Lam = closure(list(mu.keys()), e)
                free = acts_freely(Lam, G, K)
                if (abs(v - 1) < 1e-12) != free:
                    bad += 1; print('THM2 FAIL', name, len(K), v, free)
                muH = lambda H: sum(mu.get(h, 0.0) for h in H)
                fb = max(muH(H) for H in subs if acts_freely(H, G, K))
                if fb > v + 1e-12:
                    bad += 1; print('THM8 FAIL', name, len(K), fb, v)
                perm = [L for L in subs if len(L & K) == 1 and
                        len(closure(list(L) + list(K), e)) == len(L) * len(K)]
                pb = max(muH(L) for L in perm)
                if pb > v + 1e-12:
                    bad += 1; print('THM10b FAIL', name, len(K), pb, v)
                cert = max(muH(L) for L in subs if len(L & K) == 1)
                if cert > v + 1e-9:
                    gapcases.append((name, len(K), round(cert, 4), round(v, 4)))
    print('failures', bad)
    print('certificate > val cases', len(gapcases), gapcases[:10])
    print('DONE')

main()
