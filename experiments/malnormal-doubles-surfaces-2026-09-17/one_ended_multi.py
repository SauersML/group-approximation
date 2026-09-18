"""Lemma 7' (several certificates): one-endedness for C where one_ended_certificate.py is undecided.

Lemma 7' of research/malnormal-free-doubles-surface-certificates-proof.md.  Let A_1, ..., A_m be the
vertex groups pi_1(Y_j) of Lemma 6 certificates for the SAME C, and suppose D(F_2, C) acts on a tree
T with trivial edge stabilizers.  Each A_j fixes exactly one vertex w_j, and every nontrivial
element of A_j fixes only w_j.  If H fixes v and H ∩ u A_j u^-1 != 1 then u w_j = v, so
<H, u A_j u^-1> fixes v.  Starting from H_0 = A_1, the script adds
  - u, whenever H ∩ u H u^-1 != 1                        (Lemma 7), and
  - u A_j u^-1, whenever H ∩ u A_j u^-1 != 1  (|u| <= MAXLEN, including u = 1),
and reports ONE-ENDED when H = F_2.  Each witness h != 1 is checked directly: h reads a closed path
at the base of Gamma_H, and u^-1 h u reads a closed path at the base of Gamma_K.

The certificates come from search_pairs.search(C, r, first_only=False), and every one used is
re-verified by verify_lemma6.verify before it is used.
Usage: python3 one_ended_multi.py r g1 g2   (r = certificate rank; several r as "2,3")
"""
import itertools
import sys

import search_pairs as sp
from verify_lemma6 import build_Y, inv_word, inv_letter
import verify_lemma6
from one_ended_certificate import basis, reduce, fold, read

MAXLEN = 3


def witness(H_gens, K_gens, u):
    """h != 1 with h in H and u^-1 h u in K, or None."""
    GH, h0 = fold(H_gens)
    GK, k0 = fold([reduce(u + g + inv_word(u)) for g in K_gens])
    start = (h0, k0)
    path = {start: []}
    order = [start]
    for P in order:
        for x, g2 in GH[P[0]].items():
            q = GK[P[1]].get(x)
            if q is None:
                continue
            Q = (g2, q)
            if Q not in path:
                path[Q] = path[P] + [x]
                order.append(Q)
    for P in order:
        for x, g2 in GH[P[0]].items():
            q = GK[P[1]].get(x)
            if q is None:
                continue
            Q = (g2, q)
            if path[P] + [x] == path[Q] or path[Q] + [inv_letter(x)] == path[P]:
                continue
            h = reduce(path[P] + [x] + inv_word(path[Q]))
            GK0, kk = fold(K_gens)
            if h and read(GH, h0, h) == h0 and read(GK0, kk, reduce(inv_word(u) + h + u)) == kk:
                return h
            raise AssertionError("product loop is not a valid witness")
    return None


def words(maxlen):
    yield []
    for L in range(1, maxlen + 1):
        for u in itertools.product(range(4), repeat=L):
            u = list(u)
            if all(u[i] != inv_letter(u[i + 1]) for i in range(L - 1)):
                yield u


def shape(G):
    return (len(G), sorted(map(len, G)))


def certify(As, max_rounds=8):
    H = As[0]
    history = []
    for _ in range(max_rounds):
        new = []
        for u in words(MAXLEN):
            if u and witness(H, H, u) is not None:
                new.append(u)
            for K in As:
                if witness(H, K, u) is not None:
                    new.extend(reduce(u + g + inv_word(u)) for g in K)
        G, g0 = fold([g for g in H + new if g])
        history.append(len(G))
        if len(G) == 1 and len(G[0]) == 4:
            return True, history
        if shape(G) == shape(fold(H)[0]):
            return False, history
        H = basis(G, g0)
    return False, history


if __name__ == "__main__":
    ranks = [int(x) for x in sys.argv[1].split(",")]
    gens = sys.argv[2:]
    C = sp.fold_subgroup([sp.word(g) for g in gens])
    assert sp.is_malnormal(C)
    As = []
    for r in ranks:
        for cert in sp.search(C, r, first_only=False):
            ok, msg = verify_lemma6.verify(tuple(gens), cert)
            assert ok, "certificate failed independent verification"
            As.append(basis(build_Y(*cert[:3])))
    print("C", gens, "ranks", ranks, "verified certificates", len(As))
    if not As:
        sys.exit(0)
    whole, history = certify(As)
    print("vertices of Gamma_H per round", history, "=> ONE-ENDED" if whole else "=> undecided")
