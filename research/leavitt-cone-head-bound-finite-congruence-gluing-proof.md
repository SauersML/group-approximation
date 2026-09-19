---
rg: 2
id: leavitt-cone-head-bound-finite-congruence-gluing-proof
kind: route
title: Apply the positive-characteristic finiteness lemma to both cone halves, read the head on the edge group, and build the M_2(F_2) Cohn shadow from normal forms of the cones
target: leavitt-cone-head-bound-is-finite-congruence-gluing
requires:
  - positive-characteristic-steinberg-unitary-images-are-finite
  - leavitt-cuntz-cone-halves-have-rf-amalgam-cover
  - leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding
  - leavitt-cone-cover-kernel-is-dense-in-every-compact-model
---

**(1) Congruence reduction.**
- `R_+-` has characteristic 2, and `Delta_+- = E_20(R_+-)` is the image of `St_20(R_+-)`.
- Apply `positive-characteristic-steinberg-unitary-images-are-finite` with `m = 2`, `n = 20` to the composite
  `St_20(R_+-) -> Delta_+- -> U(d)`. This gives the ideals `I_+-`, the index bound `2^d`, and the finite images of the
  stated order.
- Put `P_+- = rho(Delta_+-)` and `P_0 = rho(Delta_0) <= P_+ ∩ P_-`. The maps `Delta_+- -> P_+-` agree on `Delta_0`.
  So, by the universal property of amalgams, `Gamma -> P_+ *_(P_0) P_-` is defined, and `rho` factors through it.
- An amalgam of two finite groups is virtually free.

**(2) Elementary congruence property.**
- Let `M ⊴ Delta_+` have finite index. Take the regular representation of `Delta_+/M` and apply (1).
- The level ideal `J = {a : x_ij(a) ∈ M}` has index at most `2^[Delta_+ : M]`.
- `M` is normal and contains every `x_ij(J)`, so it contains their normal closure `E_20(R_+, J)`.
- The same argument works for `Delta_-`.

**(3) Finite gluing.** A unitary representation of an amalgam is the same thing as a pair `pi_+-` of representations
of the factors, together with a unitary `u` such that `u pi_+(g) u* = pi_-(g)` for `g ∈ Delta_0`. For fixed `pi_+-`,
the admissible `u` form a torsor under the commutant of `pi_+|Delta_0`, which is `prod_chi U(m_chi)` by Schur's lemma.
By (1), `pi_+-` factor through finite quotients dominated by `St_20(B_+-)`. So `(QC)` quantifies exactly over such
triples. No property of `Delta_+-` other than its finite quotients enters.

**(4) Edge invariant.**
- `z ∈ Delta_0`. Decompose `rho|Delta_0 = ⊕ (pi_a ⊗ pi'_b)` over irreducibles of `SL_20(F_2) × SL_20(F_2)`, with
  `z = (τ, 1)` for a transvection `τ`. Then

  ```text
  ||rho(z) - 1||_2^2 = (1/d) Σ dim(pi_a) dim(pi'_b) · (2 - 2 Re χ_(pi_a)(τ) / dim pi_a).
  ```

- The bracket vanishes when `pi_a` is trivial and is at most 4 in general.
- For nontrivial `pi_a`, the kernel of `pi_a` is a proper normal subgroup of the simple group `SL_20(F_2)`, so `pi_a`
  is faithful. Then `pi_a(τ) != 1` is unitary, so `Re χ_(pi_a)(τ) < dim pi_a`.
- Taking `c_*` to be the minimum of the bracket over the finitely many nontrivial irreducibles gives `c_* > 0` and
  the two-sided bound.

**(5) Cohn shadow.**

*Normal form of `R_+`.* Let `P = F_2<s_1, s_2, q | q^2 = q, q s_1 = s_1, q s_2 = 0>`.
- These relations hold in `R`: `q s_1 = s_1 t_1 s_1 = s_1`, `q s_2 = s_1 t_1 s_2 = 0`, and `q^2 = s_1 (t_1 s_1) t_1 = q`.
  So there is an onto map `P -> R_+`.
- Rewriting `q s_1 -> s_1`, `q s_2 -> 0`, `q q -> q` pushes every `q` to the right end. So `P` is spanned by the words
  `s_μ` and `s_μ q`, for `μ` a word in `{1,2}`.
- These images are linearly independent in `R`. Let `R` act on the `F_2`-space `V` with basis `e_x`, `x ∈ {1,2}^N`, by
  `s_i e_x = e_(ix)` and `t_i e_(jx) = δ_ij e_x`. This action satisfies `t_i s_j = δ_ij` and `s_1 t_1 + s_2 t_2 = 1`,
  so `V` is a unital `R`-module.
- Choose aperiodic `x` beginning with 2 and aperiodic `y` beginning with 1. Then `μx = μ'x` forces `μ = μ'`, since
  otherwise `x = νx` with `ν` nonempty, and `x` would be periodic. The same holds for `y`.
- Now `s_μ e_x = e_(μx)` and `s_μ q e_x = 0`. So a vanishing combination `Σ a_μ s_μ + Σ b_μ s_μ q` gives
  `Σ a_μ e_(μx) = 0`, hence `a = 0`. Then applying it to `e_y` gives `b = 0`.
- Hence `P ≅ R_+`.

*The ring maps.*
- `e_11, e_21, e_11 ∈ M_2(F_2)` satisfy the relations of `P`: `e_11^2 = e_11`, `e_11 e_11 = e_11`, `e_11 e_21 = 0`. This
  gives `φ_+ : R_+ -> M_2(F_2)`.
- Set `φ_-(a) = φ_+(a^*)^T`, the composite of two anti-isomorphisms, which is a homomorphism `R_- -> M_2(F_2)`. It has
  `t_1 -> e_11`, `t_2 -> e_21^T = e_12`, and, since `q^* = q`, `q -> e_11`.
- So `φ_+ = φ_-` on `R_0 = F_2 + F_2 q`.

*The group map.*
- Entrywise `φ_+-` gives homomorphisms `Delta_+- <= GL_20(R_+-) -> GL_20(M_2(F_2)) = GL_40(F_2)`.
- They agree on `Delta_0 <= GL_20(R_0)`, so they define `rho_M` on `Gamma`.
- `rho_M(kappa) = [x_12(e_11), x_23(e_11)] x_13(e_11)^(-1) = x_13(e_11 e_11) x_13(e_11)^(-1) = 1`. In characteristic 2
  the commutator convention does not matter.
- `rho_M(z) = x_13(e_11) != 1`.
- In the regular representation of a finite group every `g != 1` has trace 0, so `||λ(g) - 1||_2^2 = 2`.

*The relation check.* `t_1 s_2 = e_11 e_21 = 0`, `t_2 s_1 = e_12 e_11 = 0`, `s_1 t_1 = e_11`, and
`s_2 t_2 = e_21 e_12 = e_22`, so `s_1 t_1 + s_2 t_2 = 1`. But `t_1 s_1 = t_2 s_2 = e_11`.

*Existence of a relator outside `ker rho_M`.* `rho_M(Gamma)` is a finite group. By
`leavitt-cone-cover-kernel-is-dense-in-every-compact-model` (2), `rho_M(K) = rho_M(Gamma)`, which contains
`rho_M(z) != 1`. Since `K` is the normal closure of the `k_i`, some `rho_M(k_i) != 1`.
