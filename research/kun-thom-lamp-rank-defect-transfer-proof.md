---
rg: 2
id: kun-thom-lamp-rank-defect-transfer-proof
kind: route
title: Read the defect lamp difference as the rank length of the rigid defect, then apply the defect rows of each approximation class
target: kun-thom-lamp-rank-certificates-force-linear-sofic-defects
requires: [kun-thom-nonsofic-wreath, kun-thom-wreath-carries-rigid-defect, sofic-groups-kill-rigid-compression-defects, compression-defect-dies-in-finite-dimensions]
---

Notation as in the target. `rk` is a Sylvester matrix rank function (Malcolmson's axioms). We use the elementary
consequences (R1)–(R3) listed in `coset-field-base-faithful-lamp-ranks-dilution-proof`: column bound,
subadditivity `rk(M + N) <= rk M + rk N`, and invariance `rk(uMv) = rk M` for invertible `u, v`.

**Imported fact (T-quot).** Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Section 1.3, as quoted in
`pgl3-nonarchimedean-lattices-property-t-citation`:
> Theorem 1.3.4 Let G1 and G2 be topological groups, and let ϕ : G1 → G2 be a continuous homomorphism with dense
> image. If G1 has Property (T), then G2 has Property (T).

Applied to discrete groups and surjections, this says that a quotient of a Kazhdan group is Kazhdan.

## Step 0: the rigid defect in the integer-lamp wreath

- A strict compressor `t` exists. If every element of `P_Γ` normalized `Γ`, then `G = <P_Γ>` would normalize `Γ`.
  Pick `γ ∈ Γ \ tΓt^-1`.
- `x_o` centralizes `Γ`, since `Γ` fixes `o = Γ`.
- `t x_o t^-1 = x_(to)` and `γ x_(to)^-1 γ^-1 = x_(γto)^-1`. So `κ = [t x_o t^-1, γ] = x_(to) x_(γto)^-1`.
- `κ ≠ 1`. Otherwise `γtΓ = tΓ`, and so `γ ∈ tΓt^-1`.

This is the computation of `kun-thom-wreath-carries-rigid-defect` with `Z` lamps in place of `Z/2` lamps. It uses
only that `Γ` is infranormal and not normal. In the group ring, `δ = x_(to) - x_(γto) = (κ - 1) x_(γto)`.

## Step 1: the rank length

For `v, w ∈ W`, put `ℓ(w) = rk(w - 1)`.
- `ℓ(vw) <= ℓ(v) + ℓ(w)`, since `vw - 1 = v(w - 1) + (v - 1)`, by (R2) and (R3).
- `ℓ(w^-1) = ℓ(w)`, since `w^-1 - 1 = -w^-1 (w - 1)`.
- `ℓ(v w v^-1) = ℓ(w)`, by (R3).

So `N = {w : ℓ(w) = 0}` is a normal subgroup, and `W_rk = W/N` is countable. Also
`rk(δ) = rk((κ - 1) x_(γto)) = ℓ(κ)` by (R3).

## Step 2: item 1 (nonsoficity)

Let `q : W -> Q` be a quotient with `q(κ) ≠ 1`.
- `q(Γ) <= q(G) <= Q`, and both are Kazhdan by (T-quot).
- `q(Γ)` is infranormal in `q(G)`: if `gΓg^-1 <= Γ` then `q(g) q(Γ) q(g)^-1 <= q(Γ)`, so `q(P_Γ)` lies in the
  compression semigroup of `q(Γ)`. It generates `q(G)`, because `P_Γ` generates `G`.
- `q(x_o) ∈ C_Q(q(Γ))`, and `[q(t) q(x_o) q(t)^-1, q(γ)] = q(κ) ≠ 1`.

So `Q` is a countable group with a rigid pair and a nontrivial rigid defect. It is not sofic by
`sofic-groups-kill-rigid-compression-defects`.
- For `q = id`, this shows that `W` is not sofic.
- For `q : W -> W_rk`, `q(κ) ≠ 1` means `ℓ(κ) > 0`, that is `rk(δ) > 0`.

## Step 3: item 2 (class kill)

- **Ring maps killing `κ`.** Let `ψ : F_p[W] -> T` be a unital ring map with `ψ(κ) = 1`, and let `rk = rk_T ∘ ψ`.
  Then `ψ(δ) = (ψ(κ) - 1) ψ(x_(γto)) = 0`, so `rk(δ) = 0`.
- **Finite-dimensional representations.** For `π : F_p[W] -> M_n(K)`, the restriction `π|_W : W -> GL_n(K)`
  is a finite-dimensional representation. It kills the whole compression-centralizer defect
  (`compression-defect-dies-in-finite-dimensions`, which covers every field and every finite dimension), and so
  it kills `κ = [t x_o t^-1, γ]`, with `t` a compressor of `Γ` and `x_o ∈ C_W(Γ)`. So `rank(π(δ)) = 0`.
  - The value at `δ` is linear in convex combinations of rank functions.
  - It is continuous under pointwise limits on matrices.
  - So it is 0 on the closed convex hull of these rank functions.
- **Sofic quotients.** If `rk = rk' ∘ F_p[q]` with `q : W -> Q` onto and `Q` sofic, then `q(κ) = 1` by Step 2
  (read contrapositively), so the first bullet applies.
- **Not base-faithful.** Base-faithful means `rk(s) = 1` for every `s ∈ S`, and `δ ∈ S`.

## Step 4: item 3 (transfer to linear soficity)

Let `Φ : F_p[W] -> U = ∏_ω M_(n_i)(K_i) / J`, where `J = {(a_i) : lim_ω rank(a_i)/n_i = 0}`, and let
`rk = rk_U ∘ Φ`, where `rk_U((a_i)) = lim_ω rank(a_i)/n_i`. By construction, `rk_U` vanishes only at 0.

**Lemma A (units lift).** Every unit of `U` has a representative `(g_i)` with every `g_i ∈ GL_(n_i)(K_i)`.
- Let `(a_i)` represent a unit `a`, and `(b_i)` represent `a^-1`.
- Then `rank(a_i b_i - 1) = ε_i n_i` with `lim_ω ε_i = 0`. So `rank(a_i) >= (1 - ε_i) n_i`.
- Write `a_i = P diag(I_r, 0) Q` with `P, Q` invertible, and put `g_i = a_i + P diag(0, I_(n_i - r)) Q`.
- Then `g_i` is invertible and `rank(g_i - a_i) <= ε_i n_i`. So `(g_i)` also represents `a`.

**The embedding.** Let `M = ∏_ω GL_(n_i)(K_i) / {(g_i) : lim_ω rank(g_i - 1)/n_i = 0}` be the rank-metric
ultraproduct group.
- The map `M -> U^×` is well defined and injective, since `(g_i) = 1` in `U` iff `(g_i - 1) ∈ J`.
- It is onto `U^×` by Lemma A.
- `Φ|_W : W -> U^×` has kernel `{w : rk_U(Φ(w) - 1) = 0} = N`.
- So `W_rk` embeds in `M`.

**Lemma B (reduction to F_p).** A countable subgroup `W'` of such an `M`, with every `K_i` of characteristic
`p`, embeds in a rank-metric ultraproduct of groups `GL_m(F_p)`.
- Enumerate `W' = {w_1, w_2, ...}`, put `F_j = {w_1, ..., w_j}`, and fix invertible representatives `g_(w,i)`.
- Let `ℓ'(w) = lim_ω rank(g_(w,i) - 1)/n_i`. It is positive for `w ≠ 1`.
- For each `j`, the following two conditions hold on an `ω`-large set of indices `i`. Choose one such `i_j`.
  - `rank(g_(ab,i) - g_(a,i) g_(b,i)) < n_i/j` for all `a, b ∈ F_j`.
  - `|rank(g_(a,i) - 1)/n_i - ℓ'(a)| < 1/j` for all `a ∈ F_j`.
- **Specialize.** Let `A_j` be the `F_p`-subalgebra of `K_(i_j)` generated by the entries of the finitely many
  matrices `g_(w,i_j)^(±1)`, with `w ∈ F_j ∪ F_j F_j`. Also adjoin the inverse of one nonzero minor of maximal size
  for each matrix `g_(ab) - g_a g_b` and `g_a - 1` above.
  - `A_j` is a nonzero finitely generated `F_p`-algebra. For a maximal ideal `m`, `A_j/m` is a field that is
    finitely generated as an `F_p`-algebra, so by the Nullstellensatz it is a finite field `F_(p^k)`.
  - Reduction mod `m` keeps each `g` invertible. It keeps each listed rank exactly: vanishing minors still vanish,
    and the chosen minor is a unit of `A_j`.
- **Restrict scalars.** `GL_n(F_(p^k)) -> GL_(nk)(F_p)` is a homomorphism that multiplies every rank by `k`, since
  an `F_(p^k)`-subspace of dimension `r` has `F_p`-dimension `kr`. So normalized ranks are unchanged.
- This gives `h_(w,j) ∈ GL_(m_j)(F_p)` with `d(h_(ab,j), h_(a,j) h_(b,j)) < 1/j` and
  `|d(h_(a,j), 1) - ℓ'(a)| < 1/j` for all `a, b ∈ F_j`, where `d` is the normalized rank distance.
- For a nonprincipal ultrafilter `ω'` on `j`, the map `w -> (h_(w,j))_j` is a homomorphism into
  `∏_ω' GL_(m_j)(F_p) / d`. It is injective because `d(h_(w,j), 1) -> ℓ'(w) > 0`.

So when `rk` is matrix-approximable, `W_rk` is `F_p`-linear sofic in the ultraproduct sense used in
`f2-linear-sofic-groups-kill-rigid-compression-defects` and in `rigid-compression-defect-normalization-dichotomy`.
If moreover `rk(δ) > 0`, then:
- `W_rk` is nonsofic, by Step 2;
- its rigid pair `q(Γ) <= q(G)` has the nontrivial defect `q(κ)`;
- so `DD(F_p-linear sofic)` fails.

## Step 5: item 4

- **Restriction.** A Sylvester rank function on `R_p` restricts to one on `F_p[W]`. Every `s ∈ S` is a unit of
  `R_p`, so `rk(s) = 1` by (R3) and `rk(1) = 1`. In particular `rk(δ) = 1`.
- **Approximability passes down.** If the rank function on `R_p` is `rk_U ∘ Φ`, its restriction is
  `rk_U ∘ (Φ|_(F_p[W]))`, which is again matrix-approximable. Step 4 then gives an `F_p`-linear sofic nonsofic
  group with `ℓ(κ) = 1`.
- **Contrapositive.** If `DD(F_p-linear sofic)` holds, Step 4 forces `rk(δ) = 0` for every matrix-approximable `rk`
  on `F_p[W]`. So no matrix-approximable rank function on `R_p` exists.

## Step 6: calibration

The group von Neumann algebra `L(W) ≅ L^∞(T^H) ⋊ G` carries the rank `rk(A) = tr(projection onto the closure of
the image of A)`. It restricts to a Sylvester rank function on `C[W]`.
- **Base-faithful.** A nonzero `s ∈ C[⊕_H Z]` is a nonzero trigonometric polynomial in finitely many variables.
  It is nonzero almost everywhere, so its image projection is 1.
- **Group-faithful.** `w - 1 ≠ 0` for `w ≠ 1`.
- **Consequence.** If it were matrix-approximable over `C`, Step 4 (with `K_i = C` and no reduction) would embed
  `W` in a complex rank-metric ultraproduct, and `W` is nonsofic by Step 2.

So in characteristic 0 the certificate that exists is of the non-approximated kind. This is why item 2 limits
methods and says nothing about whether the rank condition is true. ∎
