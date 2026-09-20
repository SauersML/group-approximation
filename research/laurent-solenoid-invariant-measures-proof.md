---
rg: 2
id: laurent-solenoid-invariant-measures-proof
kind: route
title: Average characters over column unipotents to confine Fourier mass to annihilators of rank n-1 summands, kill that mass by pigeonholing infinitely many translates whose pairwise intersections are periodic, then read Theorem C off Fubini
target: laurent-solenoid-invariant-measures-are-haar-or-periodic
requires: []
---

The notation is that of the target. The proof is self-contained. It uses only standard facts, listed here.
* (F1) A Borel probability measure on a compact metrizable abelian group is determined by its Fourier coefficients.
* (F2) Dominated convergence.
* (F3) Analytic sets are universally measurable, and a measurable set contains a Borel set of the same measure.
* (F4) Fubini–Tonelli for `mu = mu_- x mu_+`.

For `a ∈ W`, put `chi_a(xi) = (-1)^(xi(a))` and `nu^(a) = ∫ chi_a d nu`. For a subgroup `D <= W`, put
`D^perp = {xi : xi|_D = 0}`. For an `A`-submodule `H <= A^n` and an ideal `I`, put
`Z_(H,I) = (I H)^perp`. For a nonzero ideal `I`, put `X_I = (I A^n)^perp`.

## 0. Preliminaries

**(P1) Equivariance.** `L_g (D^perp) = (g D)^perp` and `nu^(g a) = (L_(g^-1) nu)^(a)`. So `Q`-invariance of `nu`
gives `nu^(g a) = nu^(a)` for all `g ∈ Q`. Also `L_g Z_(H,I) = Z_(gH, I)`.
* Proof: `(L_g xi)(g a) = xi(a)`.

**(P2) Periodic points.** For a nonzero ideal `I`:
* `A/I` is finite, so `X_I = Hom(A^n / I A^n, F_2)` is finite.
* `g (I A^n) = I A^n` for `g ∈ Q`, so `X_I` is `Q`-invariant. It is also shift-invariant, because `x` is a unit.
* A finite shift-invariant set consists of periodic points, so `X_I ⊆ Per`.
* Conversely, a point of period `p` is killed by `x^p - 1`, so it lies in `X_((x^p - 1))`.

Hence `Per = ∪_(I ≠ 0) X_I` is countable and `Q`-invariant, and `Per_p = X_((x^p-1))`, on which `Q` acts through
`SL_n(A/(x^p-1))`. Since `mu` is atomless, `mu(Per) = 0`.

**(P3) Pairwise intersections are periodic.** Let `H ≠ H'` be direct summands of `A^n` of rank `n-1`, and let
`I ≠ 0`. Then `Z_(H,I) ∩ Z_(H',I) ⊆ X_(I r)` for some `r ≠ 0`.
* Proof. `H + H'` strictly contains `H`.
* If `H + H'` had rank `n-1`, it would lie in the saturation of `H`, which is `H`, because `H` is a summand.
* So `H + H'` has rank `n`. The quotient `A^n/(H+H')` is then a finitely generated torsion module over the PID `A`,
  killed by some `r ≠ 0`, so `r A^n ⊆ H + H'`.
* Then `Z_(H,I) ∩ Z_(H',I) = (I(H+H'))^perp ⊆ (I r A^n)^perp = X_(Ir)`.

**(P4) Infinitely many translates.** Let `H_j = {c ∈ A^n : c_j = 0}`. For `k ≠ j` and `lambda ∈ A`, the elementary
matrix `g_lambda = 1 + lambda e_j e_k^T` lies in `Q`, and `g_lambda H_j = ker(e_j^T - lambda e_k^T)`.
* Proof: if `d = g_lambda c`, then `d_j - lambda d_k = c_j`.
* These are pairwise distinct rank `n-1` summands, one for each `lambda ∈ A`, since the kernels of the non-proportional
  unimodular functionals `e_j^T - lambda e_k^T` differ. This uses `n >= 2`.

## 1. Unipotent averaging (Step 1)

**Lemma 1.** Let `nu` be a `Q`-invariant finite positive measure, `a ∈ A^n`, and `j` with `a_j ≠ 0`. Put
`D = a_j H_j` and `I = (a_j)`. Then

```text
nu^(a) = ∫_(Z_(H_j, I)) chi_a d nu,      so      |nu^(a)| <= nu(Z_(H_j, I)).
```

*Proof.*
* For `c ∈ H_j`, the matrix `u_c = 1 + c e_j^T` is a product of elementary matrices, so it lies in `Q`. Also
  `u_c a = a + a_j c`.
* By (P1), `nu^(a + d) = nu^(a)` for every `d ∈ D`.
* `D` is a countable `F_2`-vector space. Exhaust it by finite subspaces `F_1 <= F_2 <= ...`.
* For a finite subgroup `F`, `|F|^(-1) Σ_(d ∈ F) chi_d = 1_(F^perp)`, by orthogonality of characters on `F`. Hence

  ```text
  nu^(a) = |F_m|^(-1) Σ_(d ∈ F_m) nu^(a+d) = ∫ chi_a 1_(F_m^perp) d nu.
  ```
* The sets `F_m^perp` decrease to `D^perp = (a_j H_j)^perp = Z_(H_j, I)`. Dominated convergence (F2) gives the
  claim. ∎

## 2. Killing the mass off the periodic points (Step 2)

Let `nu` be `Q`-invariant. Put `nu_per = nu|_Per` and `nu_1 = nu - nu_per`. Both are `Q`-invariant by (P2), and
`nu_1(Per) = 0`.

**Lemma 2.** For every `j` and every nonzero ideal `I`, `nu_1(Z_(H_j, I)) = 0`.

*Proof.*
* By (P4), the sets `Z_lambda = L_(g_lambda) Z_(H_j, I) = Z_(g_lambda H_j, I)`, for `lambda ∈ A`, all have the same
  `nu_1`-measure `m`.
* By (P3), `Z_lambda ∩ Z_lambda'` lies in the countable set `Per` for `lambda ≠ lambda'`, so it is `nu_1`-null.
* For any `K` distinct values of `lambda`, `K m = nu_1(∪ Z_lambda) <= 1`. Letting `K -> ∞` gives `m = 0`. ∎

**Proof of Theorem M.**
* For `a ≠ 0` choose `j` with `a_j ≠ 0`. Lemma 1 for `nu_1` and Lemma 2 give `nu_1^(a) = 0`.
* `nu_1(X) mu` has the same Fourier coefficients. By (F1), `nu_1 = nu_1(X) mu`.
* So `nu = c mu + nu_per` with `c = nu_1(X)`. Normalizing `nu_per` gives the stated form.
* **Ergodic measures.** `mu` is ergodic: if `E` is invariant with `0 < mu(E) < 1`, then `mu|_E / mu(E)` is
  invariant and atomless, so it equals `mu`, which contradicts `mu(X \ E) > 0`.
* If `nu` is ergodic and `0 < c < 1`, then `Per` is an invariant set of measure `1 - c`, which is a contradiction.
  So either `nu = mu`, or `nu` lives on `Per`. In the second case, ergodicity on a countable set forces a single orbit
  with uniform weight. By (P2) the orbit lies in a finite `Per_p`.
* **Independence.** An atomless invariant `nu` has `nu_per = 0`, hence `nu = mu = mu_- x mu_+`. ∎

## 3. No equivariant positive half (Theorem C)

**Corollary 0.** Let `nu` be a `Q`-invariant probability on `X` whose marginal `(pr_-)_* nu` is atomless. Then
`nu = mu`, and its conditional measures over `X_-` are a.e. `mu_+`, which is atomless. So `nu` gives measure zero to
every Borel set with countable sections over `X_-`.
* Proof: an atom `y` of `nu` would give the atom `pr_-(y)` of the marginal. So `nu` is atomless, and Theorem M gives
  `nu = mu`. The conditionals of a product measure are the second factor. The last sentence is Fubini (F4). ∎

**Proof of Theorem C.**
* Suppose `Z_0 ⊆ Z` is conull Borel and `pr_- o Phi` is countable-to-one on `Z_0`. Put `nu = Phi_* zeta`. It is
  `Q`-invariant, because `Phi` is a.e. equivariant and `zeta` is invariant.
* **`nu` is atomless.** For `y ∈ X`, `Phi^(-1)(y) ∩ Z_0 ⊆ (pr_- o Phi)^(-1)(pr_- y) ∩ Z_0`, which is countable. It is
  therefore `zeta`-null, since `zeta` is atomless. By Theorem M, `nu = mu`.
* **The image is null.** `Phi(Z_0)` is analytic, hence `mu`-measurable (F3), and `mu(Phi(Z_0)) >= zeta(Z_0) = 1`.
  Choose a Borel `B ⊆ Phi(Z_0)` with `mu(B) = 1`.
* For `x ∈ X_-`, the section `B_x = {x_+ : (x, x_+) ∈ B}` lies in `pr_+ Phi((pr_- o Phi)^(-1)(x) ∩ Z_0)`, which is
  countable. So `mu_+(B_x) = 0`, and Fubini (F4) gives `mu(B) = 0`. This is a contradiction. ∎

**Item 1 (graphs).** Given a p.m.p. action `alpha` of `Q` on `(X_-, mu_-)` and a Borel `psi` with
`L_q(x, psi(x)) = (alpha_q x, psi(alpha_q x))` a.e., apply Theorem C to `Phi(x) = (x, psi(x))`. Then
`pr_- o Phi = id` is injective, which is a contradiction. The countably-valued version is Corollary 0: no invariant
`nu` with atomless marginal lives on a set with countable sections.

**Item 2 (Laurent-realized lifts).** Let `s~ : Q -> N_-` be any homomorphism. It is a Borel p.m.p. action of `Q` on
`(X_-, mu_-)`, since `N_- <= Aut(X_-, mu_-)` (setup of `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift`).
Suppose `Phi` is equivariant from `s~` to `L` with `pr_-(Phi(x)) T_- x` a.e.
* Every `T_-`-class is countable: it is `x + V_fin^-`.
* So the fibre of `pr_- o Phi` over `x'` lies in the class of `x'`, and is countable.
* Theorem C gives a contradiction. The argument never uses `pi_- o s~ = id`, so it applies to every p.m.p. action
  of `Q` on `X_-`. ∎

## 4. Remarks (not part of the claim)

* **Calibration.** Let `B = SL_n(F_2[x])` (take `V_+` spanned by the nonnegative powers). `B` preserves `V_+`, so `L`
  preserves `X_- x {0} = V_+^perp`, and the Haar measure of `V_+^perp` is `B`-invariant.
  * Theorem M fails for `B` at (P3). Full-rank `F_2[x]`-submodules of `A^n`, such as `F_2[x]^n`, are not cofinite.
  * The compression `g -> (L_g)|_(X_- x {0})` is multiplicative, because `g^(-1)` preserves `V_+`. It is a
    Laurent-realized lift over `B` with `Phi(x) = (x, 0)`.
  * So Theorem C is exactly the statement that this half-lift mechanism, even corrected pointwise by tails, cannot
    extend to `Q`.
* **Periodic atoms and soficity.** The atoms allowed by Theorem M, the finite `Q`-sets `Per_p`, are the periodic
  models used in `bilateral-laurent-haar-relation-sofic-proof`. Theorem M says that they, together with `mu`, are
  the only invariant probabilities.
* **Scope.** The proof uses all column unipotent groups `{1 + c e_j^T : c_j = 0}` with coefficients in the whole of
  `A`, together with the elementary matrices of (P4). These generate `E_n(A) = Q`, so the proof needs all of `Q`
  (for `n = 2`, read `Q` as `E_2(A)`, which equals `SL_2(A)` because `A` is Euclidean). It does not apply to amenable
  subgroups, over which (HS) is known (`mirror-extension-lifts-over-every-amenable-subgroup`).
