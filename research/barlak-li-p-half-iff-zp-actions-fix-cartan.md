---
rg: 2
id: barlak-li-p-half-iff-zp-actions-fix-cartan
kind: claim
title: For each prime p, the UCT for M_(p^∞)-stable nuclear algebras is equivalent to order-p actions on O_2 fixing a Cartan subalgebra
distinct_from:
  barlak-li-two-half-iff-z2-actions-fix-cartan: that is the earlier Barlak--Li I theorem at the prime 2 only; this is the Barlak--Li II theorem at every prime, odd primes included, together with the one-action criterion for cyclic groups of prime power order.
  barlak-li-uct-iff-z2-z3-actions-fix-cartan: that is the joint characterization of Problem II through the primes 2 and 3; this is the prime-by-prime equivalence it is derived from.
  uct-for-two-infinity-absorbing-nuclear-algebras: that is the open UCT half at 2; this is a proved equivalence between each prime half and a statement about automorphisms of O_2.
  uct-for-three-infinity-absorbing-nuclear-algebras: that is the open UCT half at 3; this is the proved equivalence that turns it into a statement about order-three automorphisms of O_2.
artifacts:
  - research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md
---

**ESTABLISHED (literature).**  Barlak--Li, *Cartan subalgebras and the UCT
problem, II*, arXiv:1704.04939v2.

**(a) One action (Corollary 4.15).**  Let `p` be prime, `n ≥ 1`, `q = p^n`, and
let `α : Z_q ↷ O_2` be outer and strongly approximately inner.  Then
`O_2 ⋊_α Z_q` satisfies the UCT if and only if some Cartan subalgebra
`C ⊆ O_2` has `α(C) = C`, and if and only if an `α`-homogeneous inverse semigroup
model with Cantor-spectrum Cartan subalgebra exists.

**(b) One prime (Theorem 4.16).**  For every prime `p` the following are
equivalent:

1. every separable nuclear `A` that is KK-equivalent to `A ⊗ M_(p^∞)` satisfies
   the UCT;
2. every outer strongly approximately inner `Z_p`-action on `O_2` has an
   `α`-homogeneous inverse semigroup model (their condition (ii));
3. every outer strongly approximately inner `Z_p`-action on `O_2` fixes some
   Cartan subalgebra `B ⊆ O_2` globally.

Statement 1 at `p = 2` and `p = 3` is
`uct-for-two-infinity-absorbing-nuclear-algebras` and
`uct-for-three-infinity-absorbing-nuclear-algebras`: `A ⊗ M_(p^∞)` is isomorphic
to its own `M_(p^∞)`-stabilization, and a KK-equivalence transports the UCT.
Statement 3 at `p = 2` and `p = 3` is `o2-z2-actions-fix-a-cartan-subalgebra` and
`o2-z3-actions-fix-a-cartan-subalgebra`.

In the source, 3 ⟹ 1 runs as follows.  Kirchberg's Theorem I replaces `A` by a
unital `M_(p^∞)`-absorbing Kirchberg algebra `Ã`.  Barlak--Szabó (Trans. Amer.
Math. Soc. 369 (2017), Proposition 4.14) give an outer approximately
representable `γ : Z_p ↷ O_2` with `O_2 ⋊_γ Z_p ~_KK M_(p^∞)^(p-1)`.  With
`β = id_Ã ⊗ γ` on `Ã ⊗ O_2 ≅ O_2`, the crossed product is KK-equivalent to
`Ã^(p-1)`, and a `β`-invariant Cartan subalgebra gives it the UCT.  Theorem 1.4
(= Corollary 4.17) is Theorem 4.16 at `p = 2, 3` combined with Barlak--Szabó,
Proposition 4.16.  Sources and verbatim statements:
`research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md`.
