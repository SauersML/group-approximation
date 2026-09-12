---
rg: 2
id: bootstrap-class-zp-actions-on-o2-fix-a-cartan
kind: claim
title: Outer strongly approximately inner prime-power cyclic actions on O_2 in the equivariant bootstrap class fix a Cartan subalgebra
distinct_from:
  cartan-respecting-o2-automorphisms-give-uct-crossed-products: that starts from automorphisms already preserving a Cartan subalgebra and concludes the UCT; this starts from equivariant KK-equivalence with an action on a type I algebra and concludes that an invariant Cartan subalgebra exists.
  o2-z2-actions-fix-a-cartan-subalgebra: that asks it of every outer strongly approximately inner order-two action; this proves it for the actions in the equivariant bootstrap class.
artifacts:
  - research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md
---

**ESTABLISHED (derivation, this repository).**  Let `q = p^n` be a prime power and
`α : Z_q ↷ O_2` an outer strongly approximately inner action.  If `(O_2, α)` is
`KK^(Z_q)`-equivalent to a `Z_q`-action on a separable type I C\*-algebra, then some
Cartan subalgebra `C ⊆ O_2` has `α(C) = C`.

Proof: `bootstrap-class-zp-actions-on-o2-fix-a-cartan-proof`.

**Bearing on Problem II.**  The equivariant bootstrap class `B^G` consists of the
`G`-algebras `KK^G`-equivalent to actions on type I algebras (Meyer--Nadareishvili,
arXiv:2604.12529v2, introduction).  For `G` cyclic of square-free order it carries
a UCT (their Theorem 1.1).  Every class in it is represented by a pointwise outer
action on a Kirchberg algebra (Meyer, their reference [7]), and two such actions
are cocycle conjugate iff they are `KK^G`-equivalent (Gabe--Szabó, their
reference [5]).  So every outer strongly approximately inner `Z_p`-action on `O_2`
that equivariant K-theoretic classification can describe already fixes a Cartan
subalgebra.  By `barlak-li-p-half-iff-zp-actions-fix-cartan`, a counterexample at
the prime `p` must be an outer strongly approximately inner `Z_p`-action on `O_2`
that is `KK^(Z_p)`-equivalent to no action on a type I algebra.  No construction
of such an action is known.
