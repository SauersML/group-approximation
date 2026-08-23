---
rg: 2
id: fournier-facio-torsion-free-skeleton-proof
kind: route
title: Read off the compression core and saturate the simple factor
target: fournier-facio-torsion-free-skeleton
requires: []
---

## Why sufficient

**The construction.**  Verified from the full text of arXiv:2608.02025v1
(4 pages, read in full this session).  Section 2: take `U` a universal
finitely presented torsion-free group, `S` a finitely presented simple
torsion-free group, `H` a torsion-free hyperbolic group with property (T);
embed `U` into a finitely presented torsion-free Kazhdan group `P` by Osin
small cancellation over the relatively hyperbolic pair `(U * H, U)`; by
universality `P` contains `P_1 x P_2 x S` with `P_i` isomorphic to `P`; let
`E` be the double HNN extension of `P` with stable letters `u_i`
conjugating `P` to `P_i` — torsion-free, and acylindrically hyperbolic by
Minasyan--Osin; and let `pi : E -> G` be Hull's common quotient of `E` and
`H` (Corollary 7.4), finitely presented, torsion-free (Theorem 7.1(e)),
with property (T) and `pi(S) != 1`, hence `pi|_S` injective by simplicity.
In the finitely generated clause of Hull's Corollary 7.4 the output is in
`AH_0`, so the final `G` may also be retained as acylindrically hyperbolic
with trivial finite radical; this is the clause used by the later direct
saturation pass.
Setting `Gamma = pi(P)` and `t_i = pi(u_i)`, the paper records
`G = <Gamma, t_1, t_2>`, `t_i Gamma t_i^-1 <= Gamma`, and for
`J = t_1^-1 pi(S) t_1` that `[Gamma, J] = 1`, `Gamma cap J = 1` and
`t_1 J t_1^-1 = pi(S) <= Gamma` (these are exactly the hypotheses the paper needs
for the OpenAI/Kun--Thom criterion, its Proposition 1.2).

**The compression core.**  `[Gamma, J] = 1` is `comm_c` for any `c in J`;
`t_1 Gamma t_1^-1 <= Gamma` is `compresses`; property (T) of `Gamma` is
recorded in the paper.  So `KazhdanCompressionCore` is satisfied with
`t = t_1` and `c in J`.

**The simple group lies in the defect.**  Put `S' = t_1 J t_1^-1`, which with
the convention `J = t_1^-1 pi(S) t_1` is `pi(S)` on the nose.  Then
`S'` is isomorphic to `S` — simple, nonabelian,
therefore centreless — and `S' <= Gamma` by the paper's third property.  The
transported root is `d = t_1 c t_1^-1 in S'`.  Choose `c != 1`, so `d != 1`;
since `S'` is centreless there is `gamma in S'` with `[d, gamma] != 1`, and
`gamma in S' <= Gamma` is `iota gamma`.  Both `d` and `gamma` lie in `S'`,
so `[d, gamma] in S'`.  Thus `defectNormal` contains a nontrivial element of
`S'`; being normal in `G` it contains the normal closure of that element
inside `S'`, which is `S'` by simplicity.  Hence `S' <= defectNormal`.

This is the same saturation argument the repository formalized as
`FournierFacioDefectData.simpleSubgroup_le_defectNormal`, there for the
pre-quotient skeleton; the point here is that it survives to the published
torsion-free quotient because `pi|_S` is injective.  That module was deleted
temporarily during an earlier refactor but is live again in
`GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`; the declaration is
part of the current kernel-checked trust surface.  The argument above is also
self-contained.
