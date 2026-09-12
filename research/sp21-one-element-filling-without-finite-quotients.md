---
rg: 2
id: sp21-one-element-filling-without-finite-quotients
kind: claim
title: A one-element filling of an arithmetic Sp(2,1) lattice has no finite quotients
distinct_from:
  sp21-lattice-hyperbolic-quotient-without-finite-quotients: that allows any normal subgroup; this demands the normal closure of one power, a stronger shape not known to be equivalent
  sp21-lattice-has-congruence-subgroup-property: that is a property of the lattice making every filling non-residually-finite; this asks one filling to have no finite quotient at all
---

For some torsion-free cocompact arithmetic lattice `Γ < Sp(2,1)`, some
`g in Γ` and some `n >= 1`, the filling `Q = Γ/<<g^n>>` is infinite, hyperbolic
and has no nontrivial finite quotient; equivalently `<<g^n>>` is dense in `Γ̂`.

## Attempts

- **Congruence condition.**  By
  `normal-subgroups-of-arithmetic-lattices-are-congruence-open`, the congruence
  quotients of `Q` all factor through one finite group
  `Γ̄/closure(<<g^n>>)`, and density needs it trivial.  At a prime `𝔭` with
  `Γ ->> G(O/𝔭)`, if `g^n` is central mod `𝔭` then `Q` maps onto
  `G(O/𝔭)/Z != 1`.  If `n` is divisible by the order of `g` mod such a `𝔭`,
  then `g^n ≡ 1` and `Q` has that finite quotient.  So deep fillings with
  `n = N!` and `N` large are **never** finite-quotient-free.  Candidates must
  keep `g^n` non-central modulo every prime; that is a finite arithmetic check
  at each fixed `n`.
- **Non-congruence condition.**  Density also needs the closure of `<<g^n>>`
  to contain the congruence kernel `ker(Γ̂ -> Γ̄)`.  No structure controlling
  the non-congruence finite quotients of `Γ` is available here.  If the kernel
  were finite (`sp21-lattice-has-congruence-subgroup-property`), `Q` would
  already fail residual finiteness for every `g` and deep `n`.
- **Simple images decide it (2026-09-12).**
  - **The criterion.** By `filling-no-finite-quotient-iff-simple-image-orders`,
    `Q` is finite-quotient-free iff no epimorphism of `Γ` onto a finite simple
    group sends `g` to an element whose order divides `n`.
  - **What survives.** By `sp21-bounded-rank-simple-quotients-almost-all-congruence`,
    only finitely many such images have Lie rank at most `r`, for each `r`,
    beyond the congruence ones. So the families left to exclude are the
    alternating images and the images of unbounded Lie rank.
  - **The one-element shape is not needed.** Two Olshanskii quotients do the
    same job once those families are finite:
    `quotientless-hyperbolic-via-sp21-simple-quotient-bound` from
    `sp21-lattice-few-alternating-and-large-rank-quotients`.
  - **The congruence half is arithmetic.** For a fixed `g` and infinitely many
    `n`, it is a question of Ailon--Rudnick type: no prime may divide `λ^n - 1`
    for all eigenvalue ratios `λ` of `g` at once. It is not decided here.
