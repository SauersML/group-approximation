---
rg: 2
id: stable-finiteness-algebraic-bernoulli-absorption-proof
kind: route
title: Split the free module along the idempotent AB and dualize, then add bases through Seward's equal-entropy theorem
target: stable-finiteness-failure-is-algebraic-bernoulli-absorption
requires:
  - bernoulli-factor-algebraic-actions-have-finite-stabilizers
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
---

Notation as in the target; `R = F_p[G]`, and `R^n` is the left module of row vectors.
Left-module endomorphisms of `R^n` are the right multiplications `rho_C(x) = xC` by matrices
`C` in `M_n(R)`, since such a map is determined by the images of the standard basis rows.

**Duality.** Pontryagin duality is a contravariant equivalence between discrete and compact
abelian groups. It turns `G`-module maps into continuous equivariant homomorphisms, finite direct
sums into products, and isomorphisms into isomorphisms. A continuous group isomorphism preserves
Haar measure, by uniqueness of Haar measure, so it is a measure conjugacy. A character of a
`p`-torsion group takes values in the `p`-th roots of unity, identified with `F_p`. The map
`x ↦ (t ↦ (x(t e_i))_i)` identifies `X_(R^n)` with `(F_p^n)^G`, and
`(g.x)(t e_i) = x(g^-1 t e_i)` is the left shift, with Haar measure the uniform product measure.

**(1) ⇒ (2).** Let `BA = I` and `e = AB != I`.
- `e² = A(BA)B = e`, so `R^n = R^n e ⊕ R^n (I - e)`.
- `rho_B` is injective, since `xB = 0` gives `x = xBA = 0`.
- Its image is `R^n e`: `xB = x(BA)B = (xB)e` lies in `R^n e`, and `xe = (xA)B` lies in `R^n B`.
- So `R^n ≅ R^n e` and `R^n ≅ R^n ⊕ P` with `P = R^n (I - e)`. `P != 0` because a nonzero row of
  `I - e` lies in `P`. `P` is a direct summand of `R^n`, hence finitely generated projective.

Dualizing gives `(F_p^n)^G ≅ (F_p^n)^G × X_P` as compact `G`-groups.

**(2) ⇒ (1).** Dualize the isomorphism to `theta: R^n -> R^n ⊕ M`, an isomorphism of modules.
- `pi = pr_1 ∘ theta` is surjective with kernel `theta^-1(0 ⊕ M) ≅ M != 0`. Write `pi = rho_A`.
- Choose preimages under `pi` of the standard basis rows. They define `sigma = rho_B` with
  `pi ∘ sigma = id`, that is `BA = I`.
- If `AB = I`, then `xA = 0` gives `x = xAB = 0`, so `pi` is injective, a contradiction.

**(a).** The inclusion `P ⊆ R^n` dualizes to the restriction `(F_p^n)^G -> X_P`, which is surjective,
equivariant and pushes Haar measure to Haar measure. So `X_P` is a factor, and it is not a point
since `P != 0`. Nonzero elements of `R^n` have finite stabilizers (proof route of
`bernoulli-factor-algebraic-actions-have-finite-stabilizers`), and so do those of `P ⊆ R^n`.

**(b).** Let `h >= n log p`. Choose a standard probability space `(N, nu)` with
`H(N, nu) = h - n log p`: a point if `h = n log p`, any base of infinite entropy if `h = ∞`. By
`bernoulli-shifts-with-equal-base-entropy-are-isomorphic`, a Bernoulli shift with base entropy `h`
is isomorphic to `(F_p^n × N)^G = (F_p^n)^G × N^G`. Then

    (F_p^n)^G × N^G × X_P ≅ ((F_p^n)^G × X_P) × N^G ≅ (F_p^n)^G × N^G.

**(c).** Let `B_s`, `B_s'` be Bernoulli shifts with finite base entropies `s != s'` and
`X_P × B_s ≅ B_s'`. Then

    B_s' × (F_p^n)^G ≅ B_s × X_P × (F_p^n)^G ≅ B_s × (F_p^n)^G,

by the absorption `(F_p^n)^G × X_P ≅ (F_p^n)^G`. The two sides are Bernoulli shifts with base
entropies `n log p + s'` and `n log p + s`, which differ.

**`F_q`.** The regular representation `F_q -> M_d(F_p)` induces a unital ring embedding
`M_n(F_q[G]) -> M_(nd)(F_p[G])`. It preserves `BA = I` and `AB != I`.
