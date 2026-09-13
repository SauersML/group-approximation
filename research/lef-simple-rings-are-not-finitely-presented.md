---
rg: 2
id: lef-simple-rings-are-not-finitely-presented
kind: claim
title: A finitely presented simple ring that is locally embeddable into finite rings is finite
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that proves one family of crossed products is a simple LEF ring; this proves that no infinite simple LEF ring has a finite presentation, so finite presentation and the periodic-model LEF mechanism exclude each other.
  periodic-approximable-subshifts-host-no-fp-simple-group: that is a group statement about subgroups of full groups of periodically approximable subshifts; this is a ring statement about coefficient rings of elementary groups.
---

**ESTABLISHED.** Say a unital ring `R` is *LEF* if for every finite `F ⊆ R` there are a finite
unital ring `Q` and an injective map `phi : F -> Q` with `phi(0) = 0` and `phi(1) = 1` (when
`0, 1 ∈ F`), and `phi(a + b) = phi(a) + phi(b)`, `phi(-a) = -phi(a)`, `phi(ab) = phi(a) phi(b)`
whenever the operands and the result lie in `F`. A unital embedding into an algebraic
ultraproduct of finite rings makes `R` LEF.

**Theorem.** If `R` is a finitely presented unital ring that is simple and LEF, then `R` is
finite. The same holds for finitely presented algebras over a finite field `k`, with partial
maps that are also `k`-linear.

**Consequence for elementary groups.** A finitely presented infinite simple coefficient ring
has no unital embedding in an algebraic ultraproduct of finite rings. So the periodic-model
mechanism behind the infinite simple Kazhdan LEF group (`minimal-subshift-algebra-is-simple-lef-ring`)
is unavailable for any finitely presented coefficient ring. Every finite-level model of such a
ring must be approximate, not a partial homomorphism.

**Model test.**
- `F_q` is finitely presented, simple and LEF, and it is finite, as the theorem requires.
- `L_(F_2)(1,2)` is finitely presented, simple and infinite, and it is not LEF. A LEF ring is
  directly finite, because finite rings are, while `t_0 s_0 = 1 != s_0 t_0`.

**Credit.** This is the ring form of the standard fact that finitely presented LEF groups are
residually finite. Grigorchuk--Medynets (arXiv:1105.0719) use that fact to show that `[[T]]'` is
infinitely presented. No novelty is claimed; the literature was not searched for the ring form.

Route: `lef-simple-rings-are-not-finitely-presented-proof`.
