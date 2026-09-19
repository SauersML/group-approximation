"""Sanity check of the full-triple crossing count on random permutation models.

Triples T_v = (v, sigma_a v, sigma_b v), 2-of-3 rule with multiplicity.
A cheap greedy builds a contagious set S: repeatedly pick, among a random
sample of uninfected vertices, one lying in the most triples that already
have exactly one infected entry, seed it, and propagate. Records the infection
order (seeds and forced vertices interleaved). At the moment |I| = m = n/2
we count F(I) = #{v : v, sigma_a v, sigma_b v all in I}. The deterministic
lemma says F(I) >= m - |S cap I|; the first-moment lemma says w.h.p.
F(I) < 21 n / 50 for EVERY m-set. So |S| > m - 21n/50 = 2n/25.
The greedy density is an UPPER bound for the finite model's minimum.
"""
import random
import sys


def run(n, seed, sample=60):
    rng = random.Random(seed)
    A = list(range(n)); rng.shuffle(A)
    B = list(range(n)); rng.shuffle(B)
    member = [[] for _ in range(n)]
    for v in range(n):
        for w in (v, A[v], B[v]):
            member[w].append(v)
    inf = bytearray(n)
    cnt = [0] * n
    order = []
    is_seed = []
    unin = list(range(n)); pos = list(range(n))

    def remove(u):
        i = pos[u]; last = unin[-1]
        unin[i] = last; pos[last] = i; unin.pop()

    def infect(u, seedflag):
        stack = [u]; inf[u] = 1; remove(u); order.append(u); is_seed.append(seedflag)
        while stack:
            x = stack.pop()
            for t in member[x]:
                cnt[t] += 1
                if cnt[t] >= 2:
                    for w in (t, A[t], B[t]):
                        if not inf[w]:
                            inf[w] = 1; remove(w); order.append(w); is_seed.append(False)
                            stack.append(w)
    nseeds = 0
    while unin:
        cand = [unin[rng.randrange(len(unin))] for _ in range(min(sample, len(unin)))]
        best = max(cand, key=lambda u: sum(1 for t in member[u] if cnt[t] == 1))
        infect(best, True); nseeds += 1
    m = n // 2
    I = bytearray(n)
    for u in order[:m]:
        I[u] = 1
    seeds_in = sum(1 for k in range(m) if is_seed[k])
    F = sum(1 for v in range(n) if I[v] and I[A[v]] and I[B[v]])
    return nseeds, m, seeds_in, F


if __name__ == "__main__":
    for n in (2000, 10000, 40000):
        for s in range(2):
            ns, m, si, F = run(n, 1000 * n + s)
            print("n=%d seed=%d greedy density=%.4f | at |I|=n/2: F(I)=%d, "
                  "m-|S cap I|=%d, 21n/50=%d, F/n=%.4f" %
                  (n, s, ns / n, F, m - si, 21 * n // 50, F / n))
            sys.stdout.flush()
