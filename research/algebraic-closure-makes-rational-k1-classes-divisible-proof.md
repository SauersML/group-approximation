---
rg: 2
id: algebraic-closure-makes-rational-k1-classes-divisible-proof
kind: route
title: Every rational number has roots of all orders in the algebraic closure, and K_1 is abelian
target: algebraic-closure-makes-rational-k1-classes-divisible
requires:
  - leavitt-tuples-make-the-scalar-clauses-agree
  - ring-gate-k1-clause-is-unstable
  - leavitt-resolvent-k-theory-is-shifted-rational-k-theory
---

**Item 1.**
- `Q̄^x` is a divisible abelian group: for `μ in Q̄^x` and `m >= 1`, some `ν in Q̄` has `ν^m = μ`, because `Q̄` is
  algebraically closed.
- `ῑ` is a homomorphism: `ῑ(μν) = [μν] = [μ] + [ν]` in `K_1(R) = GL(R)^ab`, since the images of `μ, ν` are units of `R`.
  So `ῑ(μ) = ῑ(ν^m) = m ῑ(ν)`.
- The image of a divisible group under a homomorphism is divisible.
- `ι` is the restriction of `ῑ` to `Q^x ⊆ Q̄^x`, because the unital map `Q -> R` is unique and factors through `Q̄`.

**Item 2.** A divisible subgroup of a group with no nonzero divisible subgroup is `0`. A finitely generated abelian
group `A` has none: a divisible `D ⊆ A` satisfies `D = mD ⊆ mA` for every `m`, and `∩_m mA = 0` (take `m` a multiple of
the torsion exponent, then use that `Z^r` has no nonzero element divisible by every integer).

**Item 3.** This is the first isomorphism theorem for `ι`, together with item 1.

**Item 4.**
- Items 2 and 3, read as in `ring-gate-k1-clause-is-unstable`, give the first claim.
- By `leavitt-tuples-make-the-scalar-clauses-agree`, item 2, a ring with a Leavitt tuple has `ker ι ⊆ Λ_N(R)`. So such a
  ring cannot have `ker ι` non-finitely generated while `Λ_N` is finitely generated.
- For `R_L`, `K_1(R_L) ≅ Z` (`leavitt-resolvent-k-theory-is-shifted-rational-k-theory`).
