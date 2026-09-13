---
rg: 2
id: z2-o2-implementing-cocycle-classes-are-path-components
kind: claim
title: For an outer Z/2-action on O_2, cohomology classes of central cocycles are the path components of the cocycle space, so strong approximate innerness is a spectral-gap and connectivity condition, and a phantom disconnects 1 from −1
distinct_from:
  zp-o2-generator-kk-class-is-twisted-asymptotic-innerness: that defines the class c(α) of the implementing cocycle and identifies it with a character on the Galois components; this proves that the cohomology set is the set of path components of the cocycle space and gives spectral criteria for triviality, with no KK input.
  gabe-szabo-asymptotic-coboundary-kk-criterion: that imports the KK^G criterion for cocycles in the algebra itself; this is an elementary rigidity statement for Z/2-cocycles in the central sequence algebra.
  z2-o2-actions-anti-inner-and-o3-rokhlin-criterion: that produces anti-invariant implementing unitaries and the O_3 criterion from K-theory; this reads both, and strong approximate innerness, as connectivity statements about one space of cocycles.
---

**ESTABLISHED (derivation; standard inputs flagged in the proof; unreviewed).**
Let `α : Z/2 ↷ A = O_2` be pointwise outer with generator `σ`, and put
`A_∞ = ℓ^∞(N, A)/c_0(N, A)` and `F = A_∞ ∩ A'`, with the involution `α = α_∞`.
Let
- `Z = {z ∈ U(F) : z α(z) = 1}`, the space of `α`-cocycles, in the norm topology;
- `z ~ z'` iff `z' = v* z α(v)` for some `v ∈ U(F)`;
- `Z_0` the path component of `1`, which is the set of coboundaries.

1. **Rigidity.**  In any unital C\*-algebra with an involutive automorphism,
   two cocycles with `‖z − z'‖ < 2` are cohomologous.  An explicit unitary is
   `v = x|x|^(−1)` with `x = (1 + z z'*)/2`.  So every class is open and closed
   in `Z`.
2. **Classes are components.**  `U(F)` is path connected.  So `z ~ z'` iff `z`
   and `z'` lie in one path component of `Z`: `H^1(Z/2, U(F)) = π_0(Z)`.
3. **Implementing cocycles.**  There are unitaries `u ∈ A_∞` with
   `Ad(u)|_A = σ`.  Each gives `z_u = u* α(u) ∈ Z`, and all of them lie in one
   component `[z_α] ∈ π_0(Z)`.  This is the class `c(α)` of item 7 of
   `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness`.
4. **Spectral criteria.**  The following are equivalent:
   - `σ` is strongly approximately inner;
   - `z_α ∈ Z_0`;
   - some implementer `u` has `−1 ∉ sp(u* α(u))`;
   - some implementer `u` has `‖u − α(u)‖ < 2`;
   - some implementer `u` has `u* α(u) = exp(ih)` with `h = h* ∈ F` and
     `α(h) = −h`.

   If `‖u − α(u)‖ < 2`, then `w = h|h|^(−1)` with `h = (u + α(u))/2` is an
   `α`-invariant unitary in `A_∞` with `Ad(w)|_A = σ`.  Lifting gives unitaries
   in `O_2^α` implementing `σ` in the limit.
5. **The sign.**  `−1 ∈ Z` always, and `−z_u` is the cocycle of `u` read with
   the opposite parity.
   - `σ` is approximately inner along approximately anti-invariant unitaries iff
     `−z_α ∈ Z_0`.
   - The dual action `α̂` is strongly approximately inner iff `−1 ∈ Z_0`, that
     is, iff `F` contains a unitary `c` with `α(c) = −c`.
   - `−1 = exp(iπh)` for some self-adjoint `h ∈ F` with `α(h) = −h` iff `α` has
     the Rokhlin property.
6. **Phantom reading at `p = 2`.**  Suppose `O_2 ⋊_α Z/2 ≃_KK 0`.  By item 2(a)
   of `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`, `z_α ~ −1`.  So:
   - `α` is strongly approximately inner iff there is a norm-continuous path
     `z_s ∈ U(F)`, `s ∈ [0, 1]`, with `α(z_s) = z_s*`, `z_0 = 1` and
     `z_1 = −1`;
   - a counterexample to detection at `2` is an outer action with contractible
     crossed product whose cocycle space separates `1` from `−1`;
   - by item 5, the path cannot be an odd one-parameter group
     `s ↦ exp(iπ s h)` unless `α` is already Rokhlin.
7. **Relation to `K_0`.**  In `F ⋊_α Z/2` with implementing symmetry `λ`, the
   map `z ↦ zλ` identifies `Z` with the dual-anti-invariant symmetries.  For
   `z, z' ∈ {1, −1, z_α, −z_α}`, `z ~ z'` iff
   `[(1 + zλ)/2] = [(1 + z'λ)/2]` in `K_0(F ⋊_α Z/2)`.  For `z = 1`, `z' = −1`
   this is `2[1] = 0` in `K_0(F^α)`, the criterion of
   `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`.

**Reading.**  All forms of the open question at `p = 2` ask whether one space of
central cocycles is connected between two named points.  Rigidity (item 1)
means no approximation argument can move a cocycle across a class: two cocycles
within distance `< 2` are already cohomologous, and two different classes are at
distance exactly `2`.  So a proof must produce a global path, or a global
invariant unitary, not a small perturbation.

**Model tests.**
- *Rokhlin model.*  A Rokhlin projection `Q ∈ F` gives the odd symmetry
  `h = 2Q − 1`, and `s ↦ exp(iπ s h)` joins `1` to `−1` inside `Z`.
- *Inner action (outerness dropped).*  Take `σ = Ad(u)` with `u = u*` a unitary
  in `O_2`.  Then `α = id` on `F`, `Z` is the set of symmetries of `F`, and the
  class of `1` is `{1}`.  Every other symmetry is at distance exactly `2` from
  `1`, as item 1 predicts.  `σ` is strongly approximately inner, since `u` is
  invariant.  Item 5 fails as expected: `−1 ∉ Z_0`, and the dual action on
  `O_2 ⊗ C^2` is not strongly approximately inner.

No priority is claimed for item 1, which is the standard perturbation lemma for
finite-group cocycles.  Its reading as `π_0` and items 4–6 were not found in the
predecessor nodes.  This was a bounded check of those nodes only.

Proof: `z2-o2-implementing-cocycle-classes-are-path-components-proof`.
