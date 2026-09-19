"""Which homs rho : L_1 -> G extend to F?  (swarm-0917-w19-w19-fp-follow)

L_1 = <a, t>, t = b a b^-2.  Restriction Hom(F, G) -> Hom(L_1, G) is the
word map W(A, B) = (A, B A B^-2) on G x G.  An onto rho : L_1 -> G that
extends to sigma : F -> G can never certify a top-case (J >= L_1) violation
of (RI_{L_1}) at k = 1 (see the artifact, Proposition N).  This script
counts, for small G, the onto rho : L_1 -> G that do NOT extend.

usage: python3 extend.py
"""
from ri1 import GROUPS, closure, pmul, pinv


def word(A, B):
    return pmul(pmul(pmul(B, A), pinv(B)), pinv(B))


def main():
    for nm, (els, n) in GROUPS.items():
        N = len(els)
        img = {}
        for A in els:
            for B in els:
                img.setdefault((A, word(A, B)), []).append(B)
        onto = [(A, T) for A in els for T in els if len(closure([A, T], n)) == N]
        nonext = [p for p in onto if p not in img]
        # extensions sigma that are themselves onto G
        nonext_onto = [p for p in onto
                       if not any(len(closure([p[0], B], n)) == N for B in img.get(p, []))]
        print('%-5s |G|=%3d  |image of W|=%5d of %5d   onto rho=%5d   '
              'non-extendable onto rho=%5d   onto rho with no onto extension=%5d'
              % (nm, N, len(img), N * N, len(onto), len(nonext), len(nonext_onto)))


if __name__ == '__main__':
    main()
