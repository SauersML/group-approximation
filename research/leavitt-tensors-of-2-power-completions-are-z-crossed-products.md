---
rg: 2
id: leavitt-tensors-of-2-power-completions-are-z-crossed-products
kind: claim
title: If a Leavitt--Nekrashevych completion R has 2^b letters, then R ⊗ L_2 is a crossed product (R_0 ⊗ L_2) ⋊ Z by an explicit unit of bidegree (1, -b), so its K-theory is that of a Z-crossed product with coefficients R_0 ⊗ L_2
distinct_from:
  leavitt-tensor-powers-are-twisted-crossed-products: that decomposes L^(⊗d) itself; this decomposes R ⊗ L_2 for any completion R with 2^b letters, including the register completions R_(p,k), and the unit is written down directly.
  horner-resolvent-leavitt-tensor-k1-k2-vanish: that is the K-gate for R_2 ⊗ L; this puts that gate into the crossed-product form used for L^(⊗d) in leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees.
---

**ESTABLISHED** (lane proof, bh-algebra, elementary, not reviewed).

**Setting.** `R = O_ψ(B)` is a Leavitt--Nekrashevych completion over a field `K`, with letter set `X`,
`|X| = 2^b`, and grading `deg s_x = 1`. `R_0` is its degree-zero core. `L = L_K(1,2)` has isometries
`e_1, e_2`. Fix a bijection `μ : X -> {1,2}^b` onto words of length `b`.

**Claim.**
1. `U = Σ_(x∈X) s_x ⊗ e_(μ(x))^*` is a unit of `R ⊗ L`, with inverse `U^(−1) = Σ_x t_x ⊗ e_(μ(x))`.
   Here `e_w^*` is the co-isometry of the word `w`, and `e_w^* e_(w') = δ_(ww')` for `|w| = |w'| = b`.
2. Grade `R ⊗ L` by the degree of `R` (with `L` in degree `0`). Then `U` has degree `1`, the ring is strongly
   graded, and `R ⊗ L = ⊕_k (R_0 ⊗ L) U^k ≅ (R_0 ⊗ L) ⋊_(Ad U) Z`.
3. Consequently `K(R ⊗ L)` is the `K`-theory of a `Z`-crossed product:
   `K(R ⊗ L) ≃ hocofiber(1 − Ad U_* on K(R_0 ⊗ L)) ⊕ NK(R_0 ⊗ L; Ad U)_±`
   (Bass--Heller--Swan with twisting; ABC Theorem 3.6, Step 1).
4. `R_0 ⊗ L = colim_n M_(2^(bn))(B ⊗ L)`, so `K(R_0 ⊗ L) = colim K(L_B(1,2))`. If `B` is regular
   supercoherent, this is `0` (Ara--Cortiñas Proposition 6.2), and then
   `K(R ⊗ L) ≃ NK(R_0 ⊗ L; Ad U)_±`.

**Proof of 1.**
- `U U^(−1) = Σ_(x,y) s_x t_y ⊗ e_(μ(x))^* e_(μ(y)) = Σ_x s_x t_x ⊗ 1 = 1`.
- `U^(−1) U = Σ_(x,y) t_y s_x ⊗ e_(μ(y)) e_(μ(x))^* = Σ_x 1 ⊗ e_(μ(x)) e_(μ(x))^* = 1`, since `μ` is a
  bijection onto all words of length `b` and `Σ_(|w|=b) e_w e_w^* = 1`.

**Proof of 2.** `U` has `R`-degree `1` and is invertible. So every homogeneous component is
`(R ⊗ L)_k = (R ⊗ L)_0 U^k`, and `(R ⊗ L)_0 = R_0 ⊗ L`. ∎

**Application.** `R_(2,1)`, the algebra of `char-p-rational-function-field-in-fp-simple-algebra` for
`p = 2`, has `4 = 2^2` letters. So `R_2 ⊗ L = (R_(2,0) ⊗ L) ⋊ Z`. With `B⁺_2` regular supercoherent
(Attempt 5 of the gate), the `K`-gate for `GL_n(F_2(t))` becomes exactly the vanishing of the twisted
Nil groups of `R_(2,0) ⊗ L` in degrees `1, 2`. That is the same shape as the Farrell--Jones route of
`leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`, whose coefficient ring is
`L_0^(⊗(d−1)) ⊗ L`. There the Nils vanish by regular coherence of Laurent extensions of a semihereditary
coefficient ring.

**Lesson for general BH.** Every Leavitt--Nekrashevych host with a power-of-2 alphabet, tensored with
`L_2`, is a `Z`-crossed product whose coefficients are a Leavitt algebra over the host's own base. So the
`K`-theoretic gate for all such hosts, and hence finite presentation of their unit groups, is a single
kind of statement: coherence of Leavitt algebras over the host's base, strong enough to kill twisted
Nils. That is the input already isolated for `L^(⊗d)`. Proving it once for regular (commutative)
bases would make every register-completion host `K`-trivial at once.
