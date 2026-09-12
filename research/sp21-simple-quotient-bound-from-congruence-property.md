---
rg: 2
id: sp21-simple-quotient-bound-from-congruence-property
kind: route
title: A finite congruence kernel bounds every non-congruence simple quotient by its order
target: sp21-lattice-few-alternating-and-large-rank-quotients
requires:
  - sp21-lattice-has-congruence-subgroup-property
---

Let `C = ker(Γ̂ ->> Γ̄)` be finite. Take `r = 3`.

**Non-congruence simple quotients are finitely many.** Let `χ: Γ ->> S` be simple,
and extend it to `χ̂: Γ̂ ->> S`. If `ker χ` contains no principal congruence
subgroup, then `χ̂(C) != 1`. This image is normal in the simple group `S`, so
`χ̂(C) = S` and `|S| <= |C|`. The finitely generated group `Γ` has only finitely
many normal subgroups of bounded index.

**Congruence simple quotients have rank 3, with finitely many exceptions.** A
nonabelian simple quotient of `Γ̄ = Γ̄_S × ∏_(𝔭 ∉ S) G(O_𝔭)` factors through a
single factor.
- **A good prime `𝔭`.** The pro-`p` kernel of reduction dies in the simple
  quotient. That leaves `G(O/𝔭)/Z = PSp_6(F_q)`, of Lie rank `3`, because the
  inner form splits over the finite residue field.
- **The factor `Γ̄_S`.** Only finitely many simple quotients.
- **Abelian simple quotients.** Finitely many, since `Γ^ab` is finite.

So only finitely many simple quotients of `Γ` are alternating or of Lie rank
`> 3`. `QED`
