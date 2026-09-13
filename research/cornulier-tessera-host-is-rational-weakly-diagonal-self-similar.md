---
rg: 2
id: cornulier-tessera-host-is-rational-weakly-diagonal-self-similar
kind: claim
title: Cornulier–Tessera's quadratic-Dehn host for BS(1,2) is a finitely presented, rational, weakly diagonal self-similar group
distinct_from:
  polynomial-parameter-affine-groups-are-self-similar: that acts over Z[1/m][t_1..t_k] through parameter coordinates, where an elementary matrix with entry t has infinitely many states, so it is not rational for k >= 1; this is a two-dimensional host over Z[1/2] with no parameters, whose action is rational and weakly diagonal and whose Dehn function is quadratic.
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

**ESTABLISHED** through `cornulier-tessera-host-self-similarity-proof`. Not
independently reviewed.

**The group.** Cornulier–Tessera, arXiv:1003.0148, TeX l.126–133: with the
commuting matrices `A = 2I` and `B = [[2,1],[1,1]]`,

```text
Gamma_2 = Z[1/2]^2 x|_(A,B) Z^2 .
```

Write its elements as pairs `(M, c)` with `M in <A,B>` and `c in Z[1/2]^2`,
acting on the plane by `x -> Mx + c`.

**Claim.**
1. `Gamma_2` is finitely presented with quadratic Dehn function, and it contains
   `BS(1,2) = (Z[1/2] x {0}) x| (Z x {0})` (Cornulier–Tessera, Theorem
   `gaga`, TeX l.135–136, and l.133).
2. The affine action `(M,c) . x = Mx + c` on `Z_3^2` is faithful and preserves
   the rooted 9-ary tree of residues mod `3^j`, with alphabet `{0,1,2}^2`. It is
   self-similar: every first-level state lies in `Gamma_2`.
3. With the generating set `S = {(A,0), (B,0), (I,e_1), (I,e_2)}` the action is
   rational and weakly diagonal, in the sense of Zaremsky arXiv:2305.15176,
   Definitions at TeX l.204–205 and l.229–230.

So `Gamma_2`, which has quadratic Dehn function and contains `BS(1,2)`,
satisfies every hypothesis of Zaremsky's Corollary at TeX l.258 except
persistence, and his Lemma at TeX l.249–250 supplies persistence on the 10-ary
tree.
