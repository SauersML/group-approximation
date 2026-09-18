---
rg: 2
id: divisor-level-subpairs-cannot-certify-rank-three-twisted-cone
kind: claim
title: Subpairs of the rank-three cone that shrink the origin image by a level along a hypersurface realise the centraliser condition but never have a Kazhdan edge
distinct_from:
  block-subpairs-make-twisted-kazhdan-cones-nonsofic: that uses block subpairs, whose edge contains the constants and so has full origin image in rank three; this uses graded diagonal-twist and relative subpairs, whose origin image is a torus or trivial, and proves their edge groups are never Kazhdan.
  twisted-diagonal-cones-need-a-profinitely-invisible-core: that restricts the pair to finite-index levels of G, which all have full origin image; this restricts it to infinite-index subgroups of G whose trace on Gamma has a level along a hypersurface.
  rank-three-finite-twisted-kazhdan-cone-is-sofic: that is the open question; this kills the two candidate families it names for the nonsofic side and says what a surviving subpair must look like.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: [[divisor-level-subpairs-rank-three-twisted-cone-proof]].
It is an obstruction for the nonsofic side of [[rank-three-finite-twisted-kazhdan-cone-is-sofic]].

## Setting

`R_+ = F_q[x_1..x_d]`, `R = F_q[x_1^(±1)..x_d^(±1)]`, `Gamma = EL_3(R_+) = SL_3(R_+)`,
`G = EL_3(R) x| SL_d(Z)`, `psi = ev_0 : Gamma -> F = PSL_3(F_q)`, and
`T_3 = (F x Gamma) *_(Gamma_psi) G`.  By (B2) of [[block-subpairs-make-twisted-kazhdan-cones-nonsofic]], `T_3` is
nonsofic as soon as some `B ≤ G` has

```text
(i)  C_F(psi(C)) ≠ 1  for  C = B ∩ Gamma,      (ii) B *_C B nonsofic.
```

The only certificate for (ii) is Kun-Thom Theorem A ([[kt-pair-group-double-is-nonsofic]]): `B` and `C` Kazhdan,
`C` infranormal and not normal in `B`.

## Theorem

**(D1) Graded diagonal twists realise (i).**  Let `L ≤ Z^d` have finite index, and let `a_1, a_2, a_3 ∈ Z^d`
be pairwise distinct modulo `L` with `a_1 + a_2 + a_3 = 0`.  Put `D = diag(x^(a_1), x^(a_2), x^(a_3)) ∈ EL_3(R)`
and, for any `H ≤ Stab_(SL_d(Z))(L)`,

```text
B = D ( EL_3(F_q[L]) x| H ) D^-1  ≤  G .
```

Then `C = B ∩ Gamma = { g ∈ SL_3(R_+) : g_ij is supported on a_i - a_j + L }`, its origin image lies in the
diagonal torus, and `C_F(psi(C)) ≠ 1` for every `q`.  In the special case `L = nZ ⊕ Z^(d-1)`, `n ≥ 3`,
`a_i ∈ Z e_1`, take `H = { σ ∈ Stab(L) : σ e_1 = e_1 } ≅ Z^(d-1) x| SL_(d-1)(Z)`.  Then `B` is Kazhdan for
`d ≥ 4`, and `C` is infranormal and not normal in `B`.  So these subpairs satisfy (i) and every Kun-Thom
hypothesis **except one**.

**(D2) Their edge is never Kazhdan.**  When `L = nZ ⊕ Z^(d-1)` and every `a_i ∈ Z e_1`, the group `C` of
(D1) maps onto a Borel subgroup of `SL_3(F_q[x_2..x_d])`.  That group is infinite and solvable.  So `C` does
not have property (T), and Theorem A does not apply.

**(D3) Relative groups fail the same way.**  Let `I` be a proper nonzero ideal of `R` and `B ≤ G` any subgroup
with `EL_3(R, I) ≤ B ∩ EL_3(R) ≤ SL_3(R, I)`, and put `C = B ∩ Gamma`, `I_+ = I ∩ R_+`.
- If `R / I` is infinite, then `C` has an infinite elementary abelian quotient, through
  `g ↦ (g - 1) mod I_+^2`.  So `C` is not Kazhdan.
- If `R / I` is finite, then `I_+ + m_0 = R_+`, so `psi(C) = F` and (i) fails.

Every ideal vanishing at the origin is in the first case.  This covers the
candidates `EL_3(R, I) x| Stab(I)` named in [[finite-twisted-kazhdan-cone-is-sofic]], for every `I`, including
those vanishing at the origin.

**(D4) The mechanism.**  In (D2) and (D3), condition (i) is bought with a *level* on `C` along a hypersurface
`{f = 0}`: the congruence condition that shrinks `psi(C)` is imposed modulo a prime `P` of height one, and
`R_+ / P` is infinite.  The level then survives as an infinite amenable, or infinite abelian, quotient of `C`.

**(D5) An origin level needs an invariant pointed cone.**  Let `B ≤ G` contain `e_ij(x^m)` for all `i ≠ j` and
all `m ∈ N^d` with `|m| ≥ k`, for some `k`.  This holds when `C ⊇ Gamma(m_0^k)`, a level at the origin.  Put
`H_B = B ∩ SL_d(Z)`, the monomial part of `B`.  If the convex cone spanned by `H_B · R_+^d` is all of `R^d`,
then `e_ij(1) ∈ C` for all `i ≠ j`, so `psi(C) = F` and (i) fails.  Equivalently, (i) with an origin level
forces `H_B` to preserve a nonzero pointed closed cone `K*` in the dual orthant: `K*` is the dual of the
closed cone spanned by `H_B · R_+^d`.

For example, `Sym^2 SL_3(Z)` acting on `Sym^2 Z^3` (`d = 6`) in the basis `E_ii`, `(e_i + e_j)(e_i + e_j)^T`
preserves the positive semidefinite cone, which contains the orthant, so (D5) does not exclude
`B = <Gamma(m_0), H>`.  Whether its trace on `Gamma` is small is not settled here.  Its nonnegative monomial
elements form a finite group, so no nonnegative-compressor argument gives infranormality.  Whether some Kazhdan
`B` with an origin level and small `psi(C)` has compressors generating `B` is the case this node leaves open.

## Consequence

A Kun-Thom certificate for `T_3` needs a Kazhdan `C = B ∩ Gamma` whose origin image is small.  (D2) and (D3)
show that this cannot be done with a level along a hypersurface.  The surviving shape is a level at the
origin only, as for `ker ev_0` or `ev_0^-1(Borel)`, where `C` has finite index in `Gamma`.  There `B` must
avoid the nonnegative compressors of `SL_d(Z)`, because each of them compresses every `ev_0^-1(M)`, and by (D5)
its monomial part must preserve a pointed cone in the dual orthant.  This does not rule out every subgroup `C`
of infinite index.  It rules out the two families that have been named.
