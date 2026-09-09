---
rg: 2
id: terminated-digit-fiber-count-double-coset-proof
kind: route
title: Collapse infinite digit blocks and separate double cosets by the number of image fibers
target: terminated-digit-host-has-infinite-shell-biindex
requires:
  - fixed-base-shells-embed-in-contracting-rsg
  - terminated-digit-carries-form-finite-injection-nucleus
artifacts:
  - research/artifacts/boone-higman-spatial-overgroup-and-coset-gate-2026-09-08.md
---

Retain the graph, digit convention, and gap tokens from the required
lifting theorem. Define pi on paths with infinitely many terminators
by its gap-token correspondence. If a path has finitely many # edges,
read those completed tokens and then replace its final nonterminating
digit block by infinitely many binary zeros. This defines a surjection
pi:C_X->C. A binary point with infinitely many 1s has a singleton
fiber; an eventually-zero point has an r-root digit Cantor fiber.

The map is continuous on the dense infinitely-terminated set because
a finite number of completed tokens determines arbitrarily long binary
prefixes there. At a nonterminating block, a digit prefix of length L
forces any subsequent terminating extension to have value at least
1+h+...+h^(L-1). Its gap index is therefore at least r times that
quantity, tending to infinity. This proves continuity at the remaining
points. The lifted generators agree with the original action on the
dense token set; continuity gives pi*g = g_original*pi everywhere.
Using inverses shows that every lifted element maps each fiber onto
the fiber of the corresponding original image point.

## A prefix involution with many image fibers

Write T={1,...,h}^N for the nonterminating digit paths at Y. Then
F_p is the union of i*T over the r root edges i. Fix L>=1. Its
clopen neighborhood consisting of paths with at least L initial
digits partitions into k=r*h^L cones

    D_j = i_j*u_j*C_Y,       |u_j|=L.

Choose k distinct nonnegative integers n_j. Set

    R_j = 0*#*token(n_j)*0*C_Y.

The R_j are pairwise disjoint: gap tokens are prefix-free. They
all lie inside 0*#*C_X, which is disjoint from every D_j because
L>=1. Both D_j and R_j terminate at node Y, so canonical prefix
replacement exchanges each D_j with R_j. Perform these disjoint
swaps and act identically on the clopen complement. The resulting
involution gamma_L has only identity recurrent local actions and
therefore belongs to H_(h,r).

It maps D_j intersect F_p onto 0*#*token(n_j)*0*T. The latter
lies in the fiber of the binary point

    q_j = 1*0^(n_j)*1*0^infinity.

These q_j are distinct. All of F_p is covered by the D_j, so
pi(gamma_L(F_p)) has exactly k=r*h^L elements.

## Double-coset invariance and overgroups

For S=(E_nu)_p in its lifted marking, every s in S preserves F_p
setwise and permutes all fibers. Hence for s,t in S,

    |pi(s*gamma*t(F_p))| = |pi(gamma(F_p))|.

The strictly increasing values r*h^L separate the double cosets
S*gamma_L*S. This proves infinite bi-index in H_(h,r).

For any inclusion H_(h,r)<=J, the natural map
S\H_(h,r)/S -> S\J/S is injective: an equality of double cosets
still uses left and right factors in S, already in H_(h,r).
Thus enlarging this particular host cannot make the retained
stabilizer have finite bi-index. Enlarging the stabilizer or
changing the embedding is a different question.
