---
rg: 2
id: siefken-kari-culik-basic-construction-and-row-rigidity
kind: claim
title: Siefken's Kari--Culik minimal subsystem KC - Basic Construction points lie in KC, KC is minimal, and bottom labels determine points with irrational row angles
distinct_from:
  minimal-z2-directions-forbid-eigenvalues-vanishing-on-them: that is an eigenvalue obstruction to minimal directions for general Z^2 systems; this imports structural facts about one specific aperiodic SFT, the 13 Kari--Culik Wang tiles.
artifacts:
  - research/artifacts/siefken-kari-culik-1410-1572-excerpts.md
---

**ESTABLISHED by citation.** Source: J. Siefken, *A Minimal Subsystem of the Kari-Culik Tilings*,
arXiv:1410.1572 (Ergodic Theory Dynam. Systems, 2016). The verbatim text is in
`research/artifacts/siefken-kari-culik-1410-1572-excerpts.md`, which also records the extraction
conventions.

**Setting.**
- `K` is the set of 13 Kari--Culik Wang tiles.  The Kari--Culik tilings form a nearest-neighbour
  `Z^2` SFT that "tile[s] the plane only aperiodically" (abstract).
- `Φ` reads the bottom label of every tile and replaces `0'` by `0`.
- `KC` is the set of Kari--Culik tilings `x` whose `Φ`-rows are generalized Sturmian sequences
  (limits of rotation sequences `R_⌊⌋(α,t)_i = ⌊iα+t⌋ - ⌊(i-1)α+t⌋`).
- `KC_{Q^c} ⊆ KC` is the set of those with an irrational angle in every row.

**Imported facts.**
1. *Multiplier property* (Siefken, eq. (1)).  A tile with bottom, left, top and right labels
   `a,b,c,d` satisfies `λa + b = c + d`.  Here `λ ∈ {2, 1/3}` is the multiplier of the tile's row,
   and all tiles of a row share it.
2. *Corollary 5 and Proposition 7.*
   - Row angles obey `α_{i+1} = f(α_i)`, where `f(x) = 2x` on `[1/3,1)` and `f(x) = x/3` on `[1,2]`,
     whenever `α_i ≠ 1`.
   - The multiplier of row `i` is the `λ ∈ {1/3, 2}` with `α_{i+1} = λ α_i` (proof of Corollary 5).
     So two points with the same irrational row angles have the same multiplier in every row.
   - `f` is conjugate to the irrational rotation by `log 2/log 6`.
3. *Proposition 8 (Robinson), the Basic Construction.*  Suppose `(α_m, t_m)_{m∈Z}` has these
   properties:
   - `α_m ∈ [1/3,2]` and `t_m ∈ [0,1]`;
   - consecutive angles are related by `×2` or `/3`, with phases related by `t_{m+1} = 2t_m mod 1`
     (for `×2`) or `t_m = 3t_{m+1} mod 1` (for `/3`).

   Then there is a point of `KC` whose row `m` has bottom labels
   `⌊nα_m+t_m⌋ - ⌊(n-1)α_m+t_m⌋`, `n ∈ Z`.  A bottom label `0` is written `0'` exactly when
   `α_{m-1} ∈ [1/3,1/2]` (the prime rule), so primes depend only on the angle vector.  The same holds
   with `⌈·⌉` in place of `⌊·⌋`.  (The artifact records why the printed
   `λ_i = α_i/α_{i+1}` must be read as `α_{i+1} = λ_i α_i`.)
4. *Theorem 10.*  `Φ` restricted to `KC_{Q^c}` is one-to-one.
5. *Theorem B.*  The `Z^2` translation action on `KC` is minimal.

**Closedness.**  Not a separate import.  `KC` is closed and shift-invariant, because two sets are:
- the Kari--Culik SFT;
- the set of generalized Sturmian rows `S̄`.  This is closed by definition, and shift-invariant
  because `R(α,t)` shifts to `R(α,t+α)`.

So `KC` is a minimal subsystem of the Kari--Culik SFT.

Derivation: `siefken-kari-culik-citation`.
