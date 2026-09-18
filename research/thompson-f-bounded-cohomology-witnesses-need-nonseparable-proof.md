---
rg: 2
id: thompson-f-bounded-cohomology-witnesses-need-nonseparable-proof
kind: route
title: Monod's separable vanishing theorem, applied to the weak*-closed span of a cocycle and to the sequence l^1_0 to l^1 to R, forces non-separable witnesses and computes the l^1_0 permutation modules
target: thompson-f-bounded-cohomology-witnesses-need-nonseparable
requires: []
---

**Import (M).** Monod, arXiv:2112.13741, Theorems 1 and 2: `H^n_b(F; R) = 0` and `H^n_b(F; E) = 0` for all
`n >= 1` and every separable dual Banach `F`-module `E`. Here *dual module* means `E = (E_*)^*` with the
action dual to an isometric action on `E_*`, and *separable* means norm-separable.

**Conventions.** `F` is countable. `C^n_b(F; E) = l^∞(F^n, E)` with the usual inhomogeneous differential
`d`. A class is zero when the cocycle is `d` of a bounded cochain.

## 1. Shape of a witness

**Lemma 1.** Let `E = (E_*)^*` be a dual `F`-module and `W ⊆ E` a weak*-closed `F`-invariant subspace. Then
`W` is a dual `F`-module. If a bounded cocycle `c ∈ C^n_b(F; E)` takes values in `W`, and `[c] = 0` in
`H^n_b(F; W)`, then `[c] = 0` in `H^n_b(F; E)`.

*Proof.*
- Let `W_⊥ = {v ∈ E_* : <w, v> = 0 for all w ∈ W}`. By the bipolar theorem `W = (W_⊥)^⊥`, and
  `(E_*/W_⊥)^* ≅ (W_⊥)^⊥ = W` isometrically.
- `W` is invariant, so `W_⊥` is invariant for the predual action: `<w, g v> = <g^(-1) w, v> = 0`. So
  `E_*/W_⊥` carries an isometric quotient action. Its dual action is the restriction of the action of `E`
  to `W`.
- A bounded primitive `b ∈ C^(n-1)_b(F; W)` of `c` is also a bounded primitive in `E`. ∎

**Proposition 1 (item 1).** Let `c` be a bounded cocycle, `n >= 1`, with `[c] ≠ 0` in `H^n_b(F; E)`. Let
`V = {g · c(g_1, ..., g_n)}`, a countable set. Let `S_c` be the norm-closed span of `V` and `W_c` its
weak*-closure. Then:
- `W_c` is an `F`-invariant dual module that is not norm-separable;
- `S_c` is separable and `F`-invariant but not weak*-closed.

*Proof.*
- `V` is `F`-invariant, so `S_c` is invariant.
- Each `g` acts weak*-continuously, being the adjoint of an operator on `E_*`, so `W_c` is invariant too.
- `S_c` is separable because `V` is countable.
- Suppose `W_c` were norm-separable. By Lemma 1, `W_c` is a separable dual module and `c` takes values in
  it. (M) gives `[c] = 0` in `H^n_b(F; W_c)`, and Lemma 1 gives `[c] = 0` in `E`, a contradiction.
- If `S_c` were weak*-closed, then `W_c = S_c` would be separable, a contradiction. ∎

## 2. Killed modules (item 2)

Each module in item 2 is a separable dual module with an isometric dual action, so (M) applies.
- `l^p(X)`, `1 < p < ∞`, and `L^p(Y, μ)`, `1 < p < ∞`, are separable and reflexive.
  - A countable `F`-set `X` suffices. Every orbit of `F` is countable, and `l^p(X)` is the `l^p`-sum of
    the orbit modules. If `X` is uncountable, `l^p(X)` is not separable. The statement is then for
    countable `X`, and for the orbit summands.
  - The twisted Koopman operator `π_p(g) f = (d g_* μ / dμ)^(1/p) · f ∘ g^(-1)` is isometric on `L^p`. Its
    adjoint under the `L^p`–`L^q` pairing is `π_q(g^(-1))`, so the action is a dual action. `L^p` of a
    standard space is separable.
- `l^1(X) = c_0(X)^*` for countable `X`. The permutation action on `c_0(X)` is isometric and dualizes to
  the permutation action on `l^1(X)`.
- Separable Hilbert spaces with unitary actions are reflexive.
- For separable `H`:
  - `S_1(H) = K(H)^*` under the trace pairing. Conjugation `T ↦ u T u^*` by a unitary is isometric on
    `K(H)` and dualizes to conjugation on `S_1`.
  - `S_p`, `1 < p < ∞`, is separable and reflexive.
- Finite-dimensional isometric modules are duals of their duals.

## 3. The `l^1_0` computation (item 3)

**Long exact sequence.** Let `0 → A → B → C → 0` be a short exact sequence of Banach `F`-modules, with
bounded equivariant maps and a bounded linear (not necessarily equivariant) section `σ : C → B`. Then
`0 → l^∞(F^n, A) → l^∞(F^n, B) → l^∞(F^n, C) → 0` is exact for each `n`: compose with `σ` to lift. The
maps commute with `d`. The snake lemma gives the long exact sequence
`... → H^n_b(F; A) → H^n_b(F; B) → H^n_b(F; C) → H^(n+1)_b(F; A) → ...`.

Apply this to `0 → l^1_0(X) → l^1(X) → R → 0`, where `Σ` is the sum map and `σ(t) = t δ_x`.

- `H^0_b(F; l^1(X)) = l^1(X)^F = 0`. An invariant summable function is constant on orbits, and every orbit
  is infinite.
- `H^n_b(F; l^1(X)) = 0` for `n >= 1`, by §2 and (M). The orbit decomposition keeps the module
  separable: `F` is countable and each orbit is countable. If `X` has uncountably many orbits, write
  `l^1(X)` as the `l^1`-sum over orbits. A bounded cocycle into it takes countably many values, each
  supported on countably many points, so it lives in a separable weak*-closed summand `l^1(X_0)` with
  `X_0` a countable union of orbits. Lemma 1 and (M) kill it there.
- `H^n_b(F; R) = 0` for `n >= 1`, by (M), Theorem 1.

Exactness gives:
- `0 = H^0_b(l^1) → H^0_b(R) = R → H^1_b(l^1_0) → H^1_b(l^1) = 0`, so `H^1_b(F; l^1_0(X)) ≅ R`. The
  connecting map sends `1` to `d(σ(1)) = d δ_x = (g ↦ δ_(g x) - δ_x) = j_x`.
- For `n >= 2`: `0 = H^(n-1)_b(R) → H^n_b(l^1_0) → H^n_b(l^1) = 0`, so `H^n_b(F; l^1_0(X)) = 0`.

**The bidual.** `l^1_0(X)` is a closed subspace of `l^1(X)`. Its bidual is its weak*-closure in
`l^1(X)^** = l^∞(X)^*`, which is the annihilator of the annihilator `R · 1 ⊆ l^∞(X)`. So the bidual is
`{ξ : ξ(1) = 0}`.

- Suppose `j_x = d ξ` with `ξ` in the bidual, meaning `g ξ - ξ = δ_(g x) - δ_x` for all `g`. Then
  `μ = δ_x - ξ` is `F`-invariant with `μ(1) = 1`. Its total variation `|μ|` in the lattice `l^∞(X)^*` is
  invariant, since `g` acts by lattice isomorphisms, and `|μ|(1) >= 1`. So `|μ| / |μ|(1)` is an invariant
  mean.
- Conversely, an invariant mean `m` gives `ξ = δ_x - m` with `ξ(1) = 0` and `d ξ = j_x`.

**Separable shadows.** Let `T : l^1_0(X) → E` be bounded and equivariant, with `E` a separable dual module.
Then `T j_x` is a bounded 1-cocycle in `E`. `H^1_b(G; E) = 0` for every group `G` and every such `E`: a
bounded cocycle gives an affine isometric action with bounded orbits, and the Ryll-Nardzewski-type
fixed point theorem for separable duals (Bourbaki, TVS, IV, Appendix 3, case (c), as used in
arXiv:2112.13741, proof of Prop. 12) gives a fixed point. So `T j_x` is a coboundary. ∎

## 4. Calibration

- *Non-amenable groups of the same type.* Monod §1 and §3: Corollary 6 applies to the piecewise-projective
  groups of arXiv:1209.5229, which are non-amenable. §1–§3 above used only (M) and countability, so they
  hold verbatim for those groups. The theorem distinguishes nothing about amenability.
- *Free group.* `H^2_b(F_2; R) ≠ 0` (Brooks quasimorphisms), so item 1 for `n = 2` fails for `F_2`. The
  method uses a property that `F` has and `F_2` lacks, namely (M).
- *Sharpness of both hypotheses.* See Monod §4.C.
  - Separability: `H^2_b(G ≀ Z; l^∞(Z)) ≠ 0` whenever `H^2_b(G) ≠ 0`.
  - Duality: `H^1_b(G; l^1_0(G)) ≠ 0` for every infinite `G`. §3 shows it contains `R`.

## 5. What survives

- Shapiro's lemma for bounded cohomology (Monod, LNM 1758, §10.1) gives
  `H^n_b(F; l^∞(F/H)) ≅ H^n_b(H; R)`. A subgroup `H <= F` with `H^n_b(H; R) ≠ 0` for some `n >= 2` is
  non-amenable, so it proves `F` non-amenable. That is a witness in the non-separable module
  `l^∞(F/H)`, consistent with item 1.
- Such an `H` must violate the hypotheses of Monod's Corollary 6. Conjugating finite sets into one
  interval `Z_0` that is displaced by a single element must be impossible inside `H`.
- In degree 2 it must also have vanishing scl (Calegari: subgroups of `PL^+(I)` have `scl ≡ 0`). So the
  comparison map `H^2_b(H; R) → H^2(H; R)` is injective. The class must be a bounded ordinary 2-class of
  `H`.
