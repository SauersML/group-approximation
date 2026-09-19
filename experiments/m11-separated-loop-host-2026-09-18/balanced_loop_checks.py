#!/usr/bin/env python3
"""Finite-depth checks for m11-balanced-loop-host-has-finite-h1.

X = {1..11} coded 0..10, right actions (x w)^g = x^{pi_g} w^{g|_x}.
  alpha = (1,...,11), beta = (1,2,3,4,8)(5,10,7,11,6), M_11 = <alpha, beta>,
  b = (b, alpha, beta, 1, ..., 1),  ba = b alpha,
  C = (1, 1, 1, C, b alpha, C^-1, 1, ..., 1)   (C at letter 4, b alpha at 5, C^-1 at 6).
Checks:
 (0) |<alpha, beta>| = 7920; pick pi1 in M_11 fixing 4, 5 with 6^pi1 = 7, and pi in M_11 with
     6^pi = 4, 7^pi = 6, both written as words in alpha, beta;
 (1) C^-1 pi1^-1 C pi1 = C@6 (C^-1)@7 at depth 4;
 (2) C = pi^-1 (C^-1 pi1^-1 C pi1) pi ((b alpha)@5) at depth 4, so C lies in the normal
     closure of <M_11, b> (with (b alpha)@5 in R_0 by full self-replication of R_0);
 (3) C^m = (1,1,1,C^m,(b alpha)^m,C^-m,1,...) and C^m != 1 at depth 3 for m = 1..30.
"""
import separated_loop_checks as S

D = 11

def pm(p, q): return tuple(q[p[x]] for x in range(D))   # right action: first p then q

def m11_words():
    gens = {'a': S.ALPHA, 'b': S.BETA}
    seen = {S.IDP: ()}; frontier = [S.IDP]
    while frontier:
        nxt = []
        for p in frontier:
            for n, g in gens.items():
                q = pm(p, g)
                if q not in seen:
                    seen[q] = seen[p] + (n,); nxt.append(q)
        frontier = nxt
    return seen

def fin_word(w, n):
    g = S.ident(n)
    for l in w: g = S.mul(g, S.gen('alpha' if l == 'a' else 'beta', n))
    return g

def main():
    W = m11_words()
    assert len(W) == 7920
    pi1 = min((p for p in W if p[3] == 3 and p[4] == 4 and p[5] == 6), key=lambda p: len(W[p]))
    pi = min((p for p in W if p[5] == 3 and p[6] == 5), key=lambda p: len(W[p]))
    print("(0) |M_11| = 7920; pi1 =", ''.join(W[pi1]), "; pi =", ''.join(W[pi]))
    N = 4
    # C^-1 has sections C^-1 at 4, (b alpha)^-1 at 5, C at 6: build C recursively by hand
    cache = {}
    def Cg(n, sign):
        if n == 0: return S.ident(0)
        if (n, sign) in cache: return cache[(n, sign)]
        secs = [S.ident(n - 1)] * D; secs = list(secs)
        ba = S.gen('ba', n - 1)
        secs[3] = Cg(n - 1, sign); secs[5] = Cg(n - 1, -sign)
        secs[4] = ba if sign == 1 else S.inv(ba)
        r = S.build(S.IDP, secs, n); cache[(n, sign)] = r
        return r
    C = Cg(N, 1); Ci = Cg(N, -1)
    assert S.inv(C) == Ci
    P1 = fin_word(W[pi1], N); P = fin_word(W[pi], N)
    comm = S.mul(S.mul(Ci, S.inv(P1)), S.mul(C, P1))
    d67 = S.mul(S.at(Cg(N - 1, 1), 5, N), S.at(Cg(N - 1, -1), 6, N))
    assert comm == d67
    print("(1) [C, pi1] = C@6 (C^-1)@7 at depth", N)
    rhs = S.mul(S.mul(S.mul(S.inv(P), comm), P), S.at(S.gen('ba', N - 1), 4, N))
    assert rhs == C
    print("(2) C = pi^-1 [C, pi1] pi (b alpha)@5 at depth", N)
    n = 3; g = Cg(n, 1); ok = 0
    for m in range(1, 31):
        if g != S.ident(n): ok += 1
        g = S.mul(g, Cg(n, 1))
    # section shape of C^m
    for m in range(1, 13):
        gm = S.ident(n)
        for _ in range(m): gm = S.mul(gm, Cg(n, 1))
        assert S.section(gm, (3,), n) == S.power(Cg(n - 1, 1), m)
        assert S.section(gm, (5,), n) == S.power(Cg(n - 1, -1), m)
        assert S.section(gm, (4,), n) == S.power(S.gen('ba', n - 1), m)
    print(f"(3) C^m = (1,1,1,C^m,(b alpha)^m,C^-m,1,...) for m = 1..12; C^m != 1 at depth 3 for {ok} of m = 1..30")
    print("done")

if __name__ == "__main__":
    main()
