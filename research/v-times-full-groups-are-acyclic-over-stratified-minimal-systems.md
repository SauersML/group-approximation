---
rg: 2
id: v-times-full-groups-are-acyclic-over-stratified-minimal-systems
kind: claim
title: The full group of V times any action is acyclic after amplification, and acyclic itself whenever the action has a transfinite filtration by closed invariant sets with minimal strata; for full shifts acyclicity is equivalent to homology-injectivity of the corner copy map, and Li's minimality is needed exactly at the pattern-avoidance step
distinct_from:
  local-transposition-presentations-follow-from-superperfection: that proves LTP whenever H_2(F) = 0, and gets H_2 = 0 for minimal systems from Li; this extends the vanishing to stratified non-minimal systems, and locates exactly what fails for full shifts.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-18; lane proof given the literature inputs below; not
reviewed; no priority claimed).
- **Full shifts: OPEN.** Items 3 and 4 reduce the question and locate the obstruction.
- **Read at source:** Li, arXiv 2209.08087 v2 (PDF, §§5–6, pp. 30–41).
- **Recalled, not re-read:** Matui's Künneth formula for groupoid homology, and Szymik–Wahl [Li's ref. 90].

## Li at source: what is unconditional, and where minimality enters

- **Unconditional statements.**
  - **Theorem 5.17.** For every ample `G` with locally compact Hausdorff unit space,
    `H_*(F(R × G)) ≅ H_*(Ω^∞_0 K(𝔅_G))`, where `R` is the full equivalence relation on `N`.
  - **Theorem A (4.18).** `H̃_*(K(𝔅_G)) ≅ H_*(G)`.
  - **Corollary 6.2.** Accordingly, `F(R × G)` is rationally acyclic iff `H_*(G, Q) = 0` for `* > 0`.
- **Conditional statements.** These assume `G` minimal with comparison and no isolated units.
  - **Theorem 5.14** (Morita invariance): `F(G_U) → F(G_V)` is an `H_*`-isomorphism for nonempty compact
    open `U ⊆ V`.
  - **Theorem 5.18:** `H_*(F(R × G)) ≅ H_*(F(G))`.
  - **Corollary D = 6.8–6.10:** if `H_*(G) = 0` for all `* ≥ 0`, then `F(G)` is integrally acyclic.
- **Where minimality is used.** Minimality and comparison enter only through three steps.
  - Lemma 5.5 and Proposition 5.8(i): extending a bisection `σ` from `A ⊊ Y` to all of `Y`.
  - Theorem 5.10, the connectivity of the complex `S`: embedding the stabilizing object `u` into an
    **arbitrary small** piece `V` of a partition.
  - Theorem 5.13: a bisection from any `z` into `u^{⊕m}`.

  Everything else is Randal-Williams–Wahl stability [Li's ref. 75].

## Setting

- `H` is an ample groupoid with compact unit space `X`, and `T = G_V × H` on `Ω = C × X`.
- `F(T)` is the group of full bisections. For a non-compact unit space it is the inductive limit over
  compact opens, following Li.
- `φ_0 : F(T) → F(T)` is the corner copy map onto the elements supported in `C_0 × X`.

## Statement

1. **Amplified acyclicity, unconditional.** `F(R × T)` is integrally acyclic.
2. **Stratified acyclicity.** Suppose `X` has a transfinite decreasing filtration by closed `H`-invariant
   sets with the following properties:
   - it starts with `X_0 = X`, ends with `X_γ = ∅`, and `X_λ = ∩_(α<λ) X_α` at limit ordinals;
   - every stratum `S_α = X_α ∖ X_(α+1)` is **minimal**, meaning every `H`-orbit in `S_α` is dense in `S_α`.

   Then `F(T)` is integrally acyclic, and by the parent node LTP holds for `T`. Examples:
   - minimal `H` (a single stratum; this is the parent node);
   - one-point compactifications and other systems with finitely many orbit-closure layers;
   - countable subshifts, via the Cantor–Bendixson filtration refined one orbit at a time.

   Trivial actions are not stratified this way, since points of a Cantor set are not open, but there
   `F(T) = LC(X, V) = colim V^n` is acyclic directly.
3. **Full shifts: the reduction.** For any `H`, `F(R × T) ≅ colim(F(T), φ_0)`. Hence:
   - `F(T)` is acyclic iff `φ_0` is injective on `H_*(F(T))`;
   - in the lowest degree `k` with `H_k(F(T)) ≠ 0`, if there is one, the doubling map `D = φ_0 · φ_1`
     satisfies `D_* = 2 φ_(0*)`. So acyclicity follows if `D_*` is injective on homology.
4. **Full shifts: the obstruction.** For `H = Λ ⋉ A^Λ` with `Λ` infinite and `|A| ≥ 2`, the hypotheses of
   Li's Theorem 5.10 fail.
   - A point avoiding a pattern `p` cannot be moved into the cylinder of `p`. So the stabilizing object
     `u` does not embed into small pieces, and no fibrewise substitute works: a single bisection can
     cover whole fibres (fibre compression).
   - The orbit-closure structure of the full shift is not stratified-minimal. An open invariant set
     `U_p = {x : p occurs in x}` contains points whose orbits are not dense in `U_p`.

## Proof

**1.** `H_*(G_V) = 0`, since `G_V` is the Cuntz groupoid of `O_2` (Li, p. 5). By Künneth, `H_*(T) = 0`. By
Theorem A, `K(𝔅_T)` has vanishing reduced homology. It is connective, being the K-theory of a
permutative category, so it is contractible by Hurewicz. Then `Ω^∞_0 K(𝔅_T)` is contractible, and
Theorem 5.17 gives the claim.

**2.**
- *Restriction sequences.* Let `Y ⊆ Z` be closed invariant with `Z ∖ Y` open in `Z`. Restriction
  `F(T_Z) → F(T_Y)` is onto (descent node item 1). Its kernel consists of the elements whose arrows over
  `C × Y` are units.
  - The unit set of a compact open bisection is clopen. By the tube lemma it contains `C × O` for an open
    `O ⊇ Y`.
  - So the kernel is `F(T|_(C×(Z∖Y)))`, the elements compactly supported over `Z ∖ Y`.
- *Strata are acyclic.* `T|_(C×S_α) = G_V × H|_(S_α)` is ample, has no isolated units, and is minimal.
  - It is purely infinite. Given compact opens `U` and `W ⊇ [v] × Q`, cover `pr(U)` by finitely many
    `λ_j^-1 Q` (minimality and compactness), and carry the pieces into `[v] × Q` by distinct prefix
    extensions. So it has comparison.
  - Künneth gives `H_*(T|_(C×S_α)) = 0`. Li's Theorem 5.18 with item 1's argument then makes
    `F(T|_(C×S_α))` acyclic.
- *Transfinite induction.* Let `K_α = F(T|_(C×(X∖X_α)))`. Then `K_0 = 1`, and
  `1 → K_α → K_(α+1) → F(T|_(C×S_α)) → 1` is exact by the restriction sequence applied inside `X_α`.
  - At successor steps, the Lyndon–Hochschild–Serre spectral sequence with an acyclic kernel gives
    `H_*(K_(α+1)) ≅ H_*(F(T|_(C×S_α))) = 0`.
  - At limit steps, `K_λ = ∪_(α<λ) K_α`: a compact support in `X ∖ X_λ = ∪_α (X ∖ X_α)` lies in one
    `X ∖ X_α`. Homology commutes with directed unions.
  - Finally `K_γ = F(T)`.
- *The examples.* For countable subshifts, the Cantor–Bendixson derivatives `X^(α)` are closed and invariant.
  The isolated points of `X^(α)` form an open discrete invariant set; remove its orbits one at a time,
  each being open in what remains. Every stratum is then a single orbit, hence minimal. For trivial
  actions, `LC(X, V) = colim V^n` is acyclic by Szymik–Wahl and Künneth.

**3.**
- *The colimit.* `Pair(n) × T ≅ T`, via a prefix code identifying `C × {1, …, n}` with `C`. Under this
  identification the inclusions `Pair(n) × T ⊆ Pair(n+1) × T` become corner embeddings
  `F(T) ≅ F(T|_W) ⊆ F(T)` with `W = (cone) × X`. These are all conjugate in `F(T)` to `φ_0`, so they induce
  `φ_(0*)`.
- *The criterion.* Homology commutes with the colimit, so by 1, every class of `H_*(F(T))` dies under
  some power of `φ_(0*)`. Hence `F(T)` is acyclic iff `φ_(0*)` is injective.
- *The degree-`k` computation.* `D = μ ∘ (φ_0 × φ_1) ∘ Δ`, with commuting images.
  - In the lowest nonvanishing degree `k ≥ 2`, `H_k(F × F) = H_k ⊕ H_k` by Künneth (the lower groups
    vanish and `F` is perfect). So `D_* = φ_(0*) + φ_(1*)`.
  - `φ_1` is `φ_0` followed by conjugation by the swap `(0 1) ∈ V ≤ F`, so `D_* = 2φ_(0*)`.
  - If `D_*` is injective, so is `φ_(0*)`, and `H_k = 0`, a contradiction.

**4.**
- Take `p` nonconstant on `F`. A constant configuration `x` never contains `p`, and it is fixed by `Λ`, so
  no translate of `x` lies in `Z(F, p)`.
- The complex `S` of Li's §5.1, built from a stabilizing object whose projection contains `x`, then has
  no vertex inside a piece `[w] × Z(F, p)`. That is the step used in Theorem 5.10. ∎

## Consequences

- **Scope of LTP.** With the parent node, the local transposition presentation holds for every
  stratified-minimal system. That covers every SFT the master route produces, and countable subshifts.
- **The full-shift question** is now one sharp statement: is the corner copy map `φ_0` a homology
  isomorphism for `F(G_V × (Λ ⋉ A^Λ))`? The criterion in item 3 is `D_*` injective.
- **The master route does not need it.** P2′b for the minimal (★′) SFT goes through the gluing-group
  transport statement (bh-p2b-exact), with LTP already a theorem there.

## Lesson for general BH

**Acyclicity of V-type full groups is local in the orbit-closure lattice.** Amplification is always
acyclic, by Li. Restriction to closed invariant sets gives extensions with acyclic kernels whenever the
open strata are minimal. So every system with a well-founded minimal stratification has acyclic full
groups and a local transposition presentation.

The one place where dynamics can obstruct homological stability is **pattern avoidance**. There are
points that can never be moved into a given cylinder, and that is exactly what defeats the stability
complexes for full shifts.

The universal (full-shift) formulation of P2′b therefore carries a homological question that the actual
master-route objects do not have. Work on the minimal SFT directly.
