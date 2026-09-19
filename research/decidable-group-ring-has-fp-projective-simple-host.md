---
rg: 2
id: decidable-group-ring-has-fp-projective-simple-host
kind: claim
title: Decidable finitely presented group rings embed in rings whose rank-four projective elementary groups are finitely presented and simple
artifacts:
  - research/artifacts/boone-higman-ring-route-repair-2026-09-08.md
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
---

For every finitely presented group H with solvable word problem, there is
a finitely presented unital ring L with a unital injection Z[H] -> L
such that all three conditions hold:

1. ker(St_4(L)->EL_4(L)) is finitely normally generated in St_4(L).
2. Z(EL_4(L)) is finitely generated as a group.
3. PEL_4(L) := EL_4(L)/Z(EL_4(L)) is simple.

By [[projective-elementary-fp-kernel-criterion]], clauses 1 and 2 are
equivalent to finite presentation of PEL_4(L). Thus this formulation is
equivalent to the previous projective-host statement; it exposes exactly
which generating data the construction must provide. No centrality of the
unstable Steinberg kernel is assumed.

**OPEN.** This is a corrected sufficient hypothesis for the ring approach
to Boone--Higman. It restricts the coefficients to the actual torsion-free
additive group rings and explicitly requires both properties of the
projective target. It does not assert that ring simplicity alone supplies
them. No necessity or equivalence to Boone--Higman is claimed.

## Attempts

1. The unrestricted finite-fullness theorem is refuted by Z/6Z through
   [[ring-simple-envelope-characteristic-obstruction]]. Integral group
   rings avoid that obstruction, but the endomorphism construction gives
   no finite presentation of the resulting ring or projective group.
2. Taking EL_4(L) itself is excluded by
   [[rank-four-elementary-center-obstructs-simplicity]]. Passing to its
   center quotient avoids the exhibited involution but does not prove
   projective simplicity or finite presentation. Even if EL_4(L) is
   known finitely presented, finite normal generation of its full center
   still has to be established to invoke the quotient criterion.
3. Making one coefficient full supplies the explicit CK envelope. It
   leaves proper ideals and does not establish the projective conclusions.
4. Projectivization cannot repair failure of finite presentation of
   EL_4(L): [[fg-central-extension-of-fp-group-is-fp]] forces the
   elementary group itself to be finitely presented whenever its
   projective quotient is. The exact Steinberg-kernel and center criterion
   above now makes this part of the requested certificate explicit.
5. Projective simplicity already forces L to be a simple ring by
   [[projective-elementary-simplicity-forces-simple-ring]]. This is a
   necessary screen, not a theorem constructing L or proving the converse.
6. Calibration of the divisibility screen. Any L satisfying clause 3 is simple, and it contains Z, so Q ⊆ Z(L). Every Z-form host is therefore excluded: Leavitt, Steinberg and path algebras over Z or Z[1/m], group rings, and LC(X,Z) ⋊ Γ. Their finitely generated subrings have L/pL ≠ 0 for some prime p.
   [[finitely-presented-divisible-ring-engine]] shows that this screen is never the binding constraint. Z[H] embeds unitally in the finitely presented Q-algebra Z[H] *_Z D. So in characteristic zero the hole splits into four prerequisites, each of which can fail on its own:
   - (N1) L f.p. with Q ⊆ Z(L). This is satisfiable.
   - (N2) L simple.
   - (N3) Q^× ∩ [L^×, L^×] finitely generated. This is necessary for clause 2, by the Whitehead scalar argument.
   - (N4) the unstable Steinberg kernel is finitely normally generated.
7. Class kill for non-IBN hosts. By [[non-ibn-rational-hosts-have-infinite-elementary-centre]], every L with L ≅ L^{1+d} and Q ⊆ Z(L) has (Q^×)^d I_n ⊆ Z(EL_n(L)), so clause 2 fails. This excludes every characteristic-zero host receiving a unital Leavitt map L_Z(1,1+d) -> L, including B ⊗ L_K(1,n) over characteristic-zero fields K.
   The invariant is the rational scalar group. In characteristic p it is the finite group F_p^×, which is why the char-p Leavitt-tensor hosts do not transplant.
   Remaining host types are stably finite hosts, and purely infinite hosts with [1] of infinite order in K_0. They must still pass (N3) and (N4). No candidate is constructed here; the hole stays OPEN.
8. Class kill for finite-Hochschild-dimension hosts (swarm-0917-w19-w19-z-pull, 2026-09-19), by [[thompson-f-hosts-have-infinite-hochschild-dimension]].
   Take H = F, Thompson's group, which is f.p., decidable, and contains Z^m for every m. Since Q ⊆ Z(L), the map Q[F] -> L is injective. The m commuting translations then give w.gl.dim(L ⊗_Q Q(y_1..y_m)) >= m. The Eilenberg–Rosenberg–Zelinsky bound caps this at pd_{L^e} L. So every host has infinite Hochschild dimension over every finitely generated central subfield.
   Dead classes, including their matrix rings, corners and finite tensor products:
   - quasi-free algebras and their universal localizations;
   - LC(X,K) ⋊ G for every Cantor G-space and every G with cd_Q G < ∞. These may be stably finite, so item 7 does not reach them.
   - The invariant is the Hochschild dimension, or commuting rank. It dies at the Koszul top class in degree m.
   Survivors for H = F must have infinite Hochschild dimension and also pass item 7, for example crossed products by groups of infinite rational cd, or the free-product engine. The hole stays OPEN.
