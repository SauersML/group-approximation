#!/usr/bin/env python3
"""Antisymmetric clasp invariant: obstruction to the Push Complexity Statement CX(N).

Conventions as in experiments/loop-braid-bfmwz-push-2026-09-17/mutual_link.py:
  words in F_n are tuples of nonzero ints (i = x_i, -i = x_i^{-1});
  an automorphism is a dict i -> word; compose(f, g) = f o g;
  A(i,j) : x_i -> x_j x_i x_j^{-1}.
e_ij(phi) = exponent sum of x_j in the conjugator w_i of phi(x_i) = w_i x_i w_i^{-1} (j != i).

For u = (a,b) and z = (v,w) put
  y_c := e_cv - e_vc - e_cw + e_wc,      Phi_{u,z} := y_a - y_b
       = chi_{z,u} - chi_{u,z}   (chi as in the w9 artifact).
Checks (each prints True/False, and the script ends with ALL CHECKS PASSED):
  (A) e is additive on random products of McCool generators;
  (B) Phi_{u,z} vanishes on the generators of P_u and of P_z, and on every pair twist tau_cd
      (all ordered c != d), in particular on the w9 pushes tau_br, tau_ra;
  (C) Phi_{u,z}(A(a,v)) = 1;
  (D) Phi_{u,z} vanishes on random products of the generators in (B);
  (E) Phi_{u,z} = chi_{z,u} - chi_{u,z} on random elements.
"""
import itertools
import random
import sys


def red(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def inv(w):
    return tuple(-a for a in reversed(w))


def apply(f, w):
    out = []
    for a in w:
        img = f.get(abs(a), (abs(a),))
        out.extend(img if a > 0 else inv(img))
    return red(out)


def compose(f, g, n):
    return {i: apply(f, g.get(i, (i,))) for i in range(1, n + 1)}


def ident(n):
    return {i: (i,) for i in range(1, n + 1)}


def elt(targets, P, n):
    """(phi, phi^{-1}) for x_s -> P x_s P^{-1} (s in targets) when phi fixes the word P."""
    f, fi = ident(n), ident(n)
    for s in targets:
        f[s] = red(tuple(P) + (s,) + inv(tuple(P)))
        fi[s] = red(inv(tuple(P)) + (s,) + tuple(P))
    return (f, fi)


def mul(g, h, n):
    return (compose(g[0], h[0], n), compose(h[1], g[1], n))


def inverse(g):
    return (g[1], g[0])


def A(i, j, n):
    return elt([i], [j], n)


def e_vec(phi, n):
    """dict (i,j) -> e_ij(phi); asserts phi(x_i) is a conjugate of x_i."""
    e = {}
    for i in range(1, n + 1):
        w = red(phi.get(i, (i,)))
        L = len(w)
        assert L % 2 == 1 and w[L // 2] == i, (i, w)
        pre = w[: L // 2]
        assert red(pre + (i,) + inv(pre)) == w
        for j in range(1, n + 1):
            if j != i:
                e[(i, j)] = sum(1 if x == j else -1 if x == -j else 0 for x in pre)
    return e


def Phi(phi, a, b, v, w, n):
    e = e_vec(phi, n)
    y = lambda c: e[(c, v)] - e[(v, c)] - e[(c, w)] + e[(w, c)]
    return y(a) - y(b)


def chi(phi, u, z, n):
    (a, b), (c, d) = u, z
    e = e_vec(phi, n)
    return e[(c, a)] - e[(d, a)] - e[(c, b)] + e[(d, b)]


def cabling_gens(a, b, n):
    """Generators of P_u, u = (a,b) (w9 artifact, Section 1)."""
    gens = []
    rest = [k for k in range(1, n + 1) if k not in (a, b)]
    for i, j in itertools.permutations(rest, 2):
        gens.append(A(i, j, n))
    for k in rest:
        gens.append(elt([k], [a, b], n))       # x_k through the cable x_a x_b
    for q in rest:
        gens.append(elt([a, b], [q], n))       # x_a, x_b both conjugated by x_q
    return gens


def pair_twists(n):
    return [elt([c, d], [c, d], n) for c, d in itertools.permutations(range(1, n + 1), 2)]


def main():
    rng = random.Random(20260918)
    ok_all = True
    for n in (6, 7, 8):
        mcool = [A(i, j, n) for i, j in itertools.permutations(range(1, n + 1), 2)]
        okA = okB = okC = okD = okE = True
        # (A) additivity
        for _ in range(200):
            g = mcool[rng.randrange(len(mcool))]
            h = (ident(n), ident(n))
            for _ in range(rng.randrange(1, 6)):
                x = mcool[rng.randrange(len(mcool))]
                h = mul(h, x if rng.random() < .5 else inverse(x), n)
            eg, eh, egh = e_vec(g[0], n), e_vec(h[0], n), e_vec(mul(g, h, n)[0], n)
            okA &= all(egh[k] == eg[k] + eh[k] for k in egh)
        for a, b, v, w in itertools.permutations(range(1, n + 1), 4):
            gens = cabling_gens(a, b, n) + cabling_gens(v, w, n) + pair_twists(n)
            # (B)
            okB &= all(Phi(g[0], a, b, v, w, n) == 0 and Phi(g[1], a, b, v, w, n) == 0
                       for g in gens)
            # (C)
            okC &= Phi(A(a, v, n)[0], a, b, v, w, n) == 1
        # (D), (E) on a sample of quadruples
        quads = list(itertools.permutations(range(1, n + 1), 4))
        for a, b, v, w in rng.sample(quads, 12):
            gens = cabling_gens(a, b, n) + cabling_gens(v, w, n) + pair_twists(n)
            for _ in range(15):
                h = (ident(n), ident(n))
                for _ in range(rng.randrange(1, 7)):
                    x = gens[rng.randrange(len(gens))]
                    h = mul(h, x if rng.random() < .5 else inverse(x), n)
                okD &= Phi(h[0], a, b, v, w, n) == 0
                k = (ident(n), ident(n))
                for _ in range(rng.randrange(1, 7)):
                    x = mcool[rng.randrange(len(mcool))]
                    k = mul(k, x if rng.random() < .5 else inverse(x), n)
                okE &= Phi(k[0], a, b, v, w, n) == (chi(k[0], (v, w), (a, b), n)
                                                    - chi(k[0], (a, b), (v, w), n))
        for name, ok in (("A additivity", okA), ("B vanishing on P_u, P_z, pair twists", okB),
                         ("C Phi(A_av) = 1", okC), ("D vanishing on random products", okD),
                         ("E Phi = chi_zu - chi_uz", okE)):
            print(f"n={n} ({name}): {ok}")
            ok_all &= ok
    print("ALL CHECKS PASSED" if ok_all else "SOME CHECK FAILED")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
