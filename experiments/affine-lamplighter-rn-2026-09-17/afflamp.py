"""Affine lamplighter automata over F_p and K_infinity membership of their defining relators.

Setting (p prime, a in F_p^*): G = F_p[t, 1/t] x| <t> = Z/p wr Z acts on O = F_p[[pi]], pi = t - a,
by x -> t^n x + f(t).  With x = x_0 + pi*y (x_0 in F_p) the tree is T_p and
  B_c : x -> t*x + c   has root permutation x_0 -> a*x_0 + c and section B_c|_{x_0} = B_{x_0}.
Optionally (flag --mu) add mu_u : x -> u*x (u in F_p^*), root perm x_0 -> u*x_0, all sections mu_u.
Optionally (flag --persist) add one extra letter p, fixed by every generator, with s|_p = s (the persistent
extension of Skipper-Witzel-Zaremsky, Lemma 5.3): the group is unchanged, but then K_infinity = 1, so every
nontrivial relator must come out 'in N: True  in K_inf: False'.

Relators checked (tau = B_1 B_0^-1, A = B_0, d_k = A^k tau A^-k):
  (T)  B_c B_0^-1 (B_0 B_1^-1)^c          c = 2..p-1   (B_c = tau^c A)
  (P)  tau^p
  (L)  [tau, d_k]                          k = 1..K
  (M)  with --mu: mu_g^(p-1), mu_g B_c mu_g^-1 = ?  (see below)
Each relator is tested for membership in N (acts trivially) and in K_infinity (acyclic section graph).
Run: python3 afflamp.py p a [K] [--mu] [--persist]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'nonc-rn-fp-2026-09-17'))
from autom import Automaton


def build(p, a, mu=False, persist=False):
    gens = {}
    for c in range(p):
        perm = tuple((a * x + c) % p for x in range(p))
        gens[f'B{c}'] = (perm, tuple(f'B{x}' for x in range(p)))
    if mu:
        for u in range(1, p):
            if u == 1:
                continue
            gens[f'm{u}'] = (tuple((u * x) % p for x in range(p)), tuple(f'm{u}' for _ in range(p)))
    if persist:
        gens = {n: (perm + (p,), secs + (n,)) for n, (perm, secs) in gens.items()}
        return Automaton(p + 1, gens)
    return Automaton(p, gens)


def main():
    args = [x for x in sys.argv[1:] if not x.startswith('--')]
    mu = '--mu' in sys.argv
    persist = '--persist' in sys.argv
    p = int(args[0]); a = int(args[1]) % p
    K = int(args[2]) if len(args) > 2 else 6
    assert a != 0
    Au = build(p, a, mu, persist)
    B = lambda c: (Au.idx[f'B{c % p}'],)
    inv = lambda w: tuple(-u for u in reversed(w))
    comm = lambda x, y: x + y + inv(x) + inv(y)
    pw = lambda w, n: w * n if n >= 0 else inv(w) * (-n)
    A = B(0)
    tau = B(1) + inv(B(0))
    d = lambda k: pw(A, k) + tau + pw(A, -k)
    rels = []
    for c in range(2, p):
        rels.append((f'T{c}', B(c) + inv(B(0)) + pw(B(0) + inv(B(1)), c)))
    rels.append(('P', pw(tau, p)))
    for k in range(1, K + 1):
        rels.append((f'L{k}', comm(tau, d(k))))
    if mu:
        # generator g of F_p^*
        g = next(u for u in range(2, p) if len({pow(u, e, p) for e in range(1, p)}) == p - 1) if p > 2 else None
        if g is not None:
            m = (Au.idx[f'm{g}'],)
            rels.append(('Mord', pw(m, p - 1)))
            # mu_g B_c mu_g^-1 : x -> g*(t*(x/g) + c) = t x + g c, so equals B_{gc}
            for c in range(p):
                rels.append((f'Mconj{c}', m + B(c) + inv(m) + inv(B(g * c))))
            for u in range(2, p):
                if u != g:
                    e = next(e for e in range(1, p) if pow(g, e, p) == u)
                    rels.append((f'Mpow{u}', (Au.idx[f'm{u}'],) + inv(pw(m, e))))
    allK = True
    for name, w in rels:
        inN = Au.is_trivial(w)
        inK = Au.in_K_inf(w) if inN else False
        allK &= inK
        print(f'p={p} a={a} {name:7s} len={len(Au.reduce(w)):3d} in N: {inN}  in K_inf: {inK}  reach={len(Au.reach(w))}')
    print('ALL IN K_inf:', allK)


if __name__ == '__main__':
    main()
