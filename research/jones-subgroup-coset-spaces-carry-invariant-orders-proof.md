---
rg: 2
id: jones-subgroup-coset-spaces-carry-invariant-orders-proof
kind: route
title: Leaf digit sums make every pairwise disagreement set of digit-sum colourings start at a dyadic point, and comparing colours there is an F-invariant lexicographic order
target: jones-subgroup-coset-spaces-carry-invariant-orders
requires: [thompson-f-known-maximal-subgroups-are-jones-pullbacks]
artifacts:
  - experiments/thompson-f-2-transitive-2026-09-17/jones_coset_order_check.py
---

**Notation.**
- For a finite binary word `w`, put `[w] = [.w, .w + 2^{−|w|})` and let `ds(w)` be its number of
  ones.
- For `x ∈ D`, `ds(x)` is the number of ones in the terminating expansion of `x`. Appending zeros
  does not change `ds`, so `ds(.w) = ds(w)`.
- `g ∈ F` with tree pair `w_i → v_i` (`i = 1, …, k`, left to right) maps `[w_i]` affinely onto
  `[v_i]`, with `g(.w_i u) = .v_i u` for every finite word `u`.

**Step 1 (leaf formula).** Let `x ∈ [v_i] ∩ D`. Write the expansion of `x` with at least `|v_i|`
digits by padding zeros. Its first `|v_i|` digits are `v_i`, so `x = .v_i u` for a finite word
`u`, and `g^{-1}x = .w_i u`. Then

`(g·c_n)(x) − c_n(x) = ds(w_i u) − ds(v_i u) = ds(w_i) − ds(v_i)  (mod n)`.

The first leaves are `w_1 = 0^a` and `v_1 = 0^b`, so `ds(w_1) = ds(v_1) = 0`. Hence
`δ_g := g·c_n − c_n` is a step function, constant on each `[v_i] ∩ D`, and zero on `[0, 2^{−b})`.
If `δ_g ≠ 0`, its support has least element `m(g) = .v_i` for the least `i` with
`ds(w_i) ≢ ds(v_i)`. This point lies in `D`, because `i ≥ 2`.

**Step 2 (all pairs).** Let `φ = a·c_n ≠ ψ = b·c_n`. Then

`ψ − φ = a·(a^{-1}b·c_n − c_n) = δ_{a^{-1}b} ∘ a^{-1}`,

so `{φ ≠ ψ} = a({δ_{a^{-1}b} ≠ 0})`. Since `a` is an increasing bijection of `D`, this set has the
least element `μ(φ,ψ) = a(m(a^{-1}b))`.

**Step 3 (order).** Define `φ ≺ ψ` iff `φ(μ) < ψ(μ)` in `{0, …, n−1}`, where `μ = μ(φ,ψ) = μ(ψ,φ)`.
- *Trichotomy.* `φ(μ) ≠ ψ(μ)`, so exactly one of `φ ≺ ψ` and `ψ ≺ φ` holds.
- *Transitivity.* Let `φ_1 ≺ φ_2` at `x = μ(φ_1,φ_2)` and `φ_2 ≺ φ_3` at `y = μ(φ_2,φ_3)`.
  - If `x < y`: `φ_3 = φ_2` on `D ∩ (0, x]`, so `φ_3` agrees with `φ_1` below `x` and
    `φ_3(x) = φ_2(x) > φ_1(x)`.
  - If `y < x`: `φ_1 = φ_2` on `D ∩ (0, y]`, so `φ_1` agrees with `φ_3` below `y` and
    `φ_1(y) = φ_2(y) < φ_3(y)`.
  - If `x = y`: all three agree below `x` and `φ_1(x) < φ_2(x) < φ_3(x)`.

  In every case `μ(φ_1,φ_3)` exists by Step 2 and `φ_1 ≺ φ_3`.
- *Invariance.* For `f ∈ F`, `{f·φ ≠ f·ψ} = f({φ ≠ ψ})`, so `μ(f·φ, f·ψ) = f(μ(φ,ψ))`. Also
  `(f·φ)(f μ) = φ(μ)`, so `f·φ ≺ f·ψ` iff `φ ≺ ψ`.

**Step 4 (identification and pullbacks).**
- `a·c_n ↦ a Stab_F(c_n)` identifies `F·c_n` with `F/Stab_F(c_n)`, and
  `Stab_F(c_n) = \vec F_n` by item 1 of `thompson-f-known-maximal-subgroups-are-jones-pullbacks`.
- For a homomorphism `ψ : F → F` and `H = ψ^{-1}(\vec F_n)`, the map `aH ↦ ψ(a)·c_n` is well
  defined and injective: `aH = bH` iff `ψ(a^{-1}b) ∈ \vec F_n` iff `ψ(a)·c_n = ψ(b)·c_n`. It
  intertwines left multiplication by `f` with the action of `ψ(f)`. So the order pulled back to
  `F/H` is `F`-invariant.
- For a conjugate `gHg^{-1}`, the `F`-set `F/gHg^{-1}` is isomorphic to `F/H` via `x gHg^{-1} ↦ xgH`.

**Step 5 (no 2-transitivity).** Let `F` act 2-transitively on `Ω` with `|Ω| ≥ 2`, and suppose `Ω`
carries an `F`-invariant total order. Take `x ≺ y` and `f` with `(fx, fy) = (y, x)`. Invariance
gives `fx ≺ fy`, that is `y ≺ x`, a contradiction. So a point stabilizer of a 2-transitive action
never has an `F`-invariant order on its coset space. Items 2 and 3 of
`thompson-f-known-maximal-subgroups-are-jones-pullbacks` present the Golan–Sapir and Golan maximal
subgroups as `ψ^{-1}(\vec F_n)`, with `n = 2` and `n = p` respectively. For `Stab(α)`, the orbit
`F·α ⊂ (0,1)` with the order of the reals is an invariant order on `F/Stab(α)`.
