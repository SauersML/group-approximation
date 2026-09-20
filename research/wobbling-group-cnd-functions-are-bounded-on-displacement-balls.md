---
rg: 2
id: wobbling-group-cnd-functions-are-bounded-on-displacement-balls
kind: claim
title: "Every cnd function on the wobbling group of Z (or of any set of Z-orbits) is bounded on each displacement ball of constant flux; so no cnd function of an ambient orbit wobbling group restricts to a proper one on the full-shift topological full group"
distinct_from:
  wobbling-normal-relative-t-subgroups-are-locally-finite: that restricts refutation witnesses (normal relative-(T) pairs inside W(Z)); this restricts proof witnesses, showing that every cnd function defined on all of W(Z) is bounded on displacement balls, so a proper cnd function on a subgroup of W(Z) can never be the restriction of one on W(Z)
  subshift-crossed-product-gl-has-no-distorted-elements: that says displacement grows along cyclic subgroups of topological full groups; this says the whole ambient group W(Z) is coarsely bounded on displacement balls for every Hilbert-space action, a statement about W(Z) and not about finitely generated subgroups
  full-shift-topological-full-group-is-a-t-menable: that asks for a proper cnd function on [[X]]; this proves that no such function extends to the orbit wobbling group, so any witness must use more than bounded displacement along orbits
---

**ESTABLISHED** by `wobbling-cnd-bounded-on-displacement-balls-proof`. One imported theorem
(Cornulier 2006) is cited verbatim there.

## Setting

- `I` is any nonempty set, and `Y = Z × I`. `W(Y)` is the group of bijections `π` of `Y` that
  preserve each fibre `Z × {i}` and have finite displacement
  `disp(π) = sup_{(n,i)} |π_1(n,i) − n|`, where `π(n,i) = (π_1(n,i), i)`. For `I` a singleton this
  is the wobbling group `W(Z)`. A countable union of aperiodic orbits of a `Z`-action, with a base
  point chosen in each orbit, is such a `Y`, and its orbit wobbling group is `W(Y)`.
- `σ ∈ W(Y)` is the shift `(n,i) ↦ (n+1,i)`.
- **Flux.** For `π ∈ W(Y)`, a fibre `i` and a cut `m ∈ Z`, let `F = #{n < m : π_1(n,i) ≥ m}` and
  `B = #{n ≥ m : π_1(n,i) < m}`. Then `φ_i(π) = F − B` does not depend on `m`, and
  `φ(π) = (φ_i(π))_i` is a homomorphism `W(Y) → ℓ^∞(I, Z)` with `φ(σ) = (1,1,…)` and
  `|φ_i(π)| ≤ disp(π)`.
- A cnd function is a function `ψ: G → R` with `ψ(g^{-1}) = ψ(g)` and
  `Σ_{i,j} c_i c_j ψ(g_i^{-1} g_j) ≤ 0` whenever `Σ c_i = 0`. No continuity or measurability is
  assumed; `W(Y)` is treated as a discrete group.

## Statement

1. **(Bounded on balls of constant flux.)** Let `ψ` be any cnd function on `W(Y)` and `r ≥ 0`. Then
   `ψ` is bounded on `W_r^0 = {π ∈ W(Y) : disp(π) ≤ r and φ(π) is a constant vector}`. For `I` a
   singleton, `W_r^0` is the whole displacement ball `W_r`, so *every cnd function on `W(Z)` is
   bounded on every `W_r`*.
2. **(Decomposition behind it.)** Let `L` be even with `L > 4r` and `L ≥ 6`. Then
   `W_r^0 ⊆ ⋃_{|j| ≤ r} σ^j · σ^{L/2} P σ^{-L/2} · P`, where `P ≅ Π_{Z × I} S_L` is the group of
   permutations preserving every block `[kL, (k+1)L) × {i}`. Moreover
   `P ⊆ A · Q' · Q` for three subgroups isomorphic to `A_L^{Z×I}` or `A_{2L}^{Z×I}`, each strongly
   bounded by Cornulier's theorem.
3. **(Full shift.)** Let `X = {0,1}^Z`, `[[X]]` its topological full group, and `Y` any nonempty
   σ-invariant set of aperiodic points (for instance one dense orbit, or all aperiodic points), made
   into `Z × I` by choosing base points. Let `ι: [[X]] → W(Y)` be restriction,
   `ι(g)(σ^n y) = σ^{n + k_g(σ^n y)} y`. Then `φ(ι(g))` is constant for every `g`, and
   `disp(ι(g)) ≤ ‖k_g‖_∞`. Hence for every cnd function `ψ` on `W(Y)`, `ψ ∘ ι` is bounded on
   `B_1 = {g ∈ [[X]] : ‖k_g‖_∞ ≤ 1}`, which is infinite. So **`ψ ∘ ι` is not proper**.

## Role (class-kill for proofs of `full-shift-topological-full-group-is-a-t-menable`)

- **Class killed.** Proper cnd functions on `[[X]]` obtained by restricting a cnd function defined
  on the whole orbit wobbling group `W(Y)`, for any set `Y` of aperiodic points. This covers every
  wall structure, median space or Hilbert action on which all bounded-displacement permutations of
  the orbits act: half-line commensurating actions, weighted wall sums over orbit cuts, finite sums
  of pullbacks along several dense orbits, and so on. It also corrects the remark in the Known
  section of the full-shift node that Haagerup for `W(Z)` would imply that claim. By item 1, `W(Z)`
  is as far from Haagerup as it can be along its displacement bornology. (An uncountable discrete
  group has no proper function in any case.)
- **Invariant.** The displacement bornology of `W(Y)`, restricted to constant flux, is bounded for
  every isometric action on a Hilbert space. The reason is that block-permutation groups are
  infinite powers of finite perfect groups, which are strongly bounded.
- **Where every member dies.** On the small-support involutions `g_m ∈ B_1` of the w16 attempt
  (swap a deep cylinder `E_m` around an aperiodic point with `σE_m`). They all lie in `ι^{-1}(W_1^0)`.
- **Survivors.**
  - A cnd function on `[[X]]` that is *not* the restriction of one on `W(Y)`. For instance, a
    countable sum `Σ_i ψ_i ∘ ι_i` over orbits, where each term is bounded on `B_r` but the bounds
    `C_i(r)` diverge. Such a sum is finite on `[[X]]` because the local rules `k_g` are continuous,
    and it is not defined on `W(Y)`.
  - Any proper witness must therefore use the continuity of `k_g` in an essential way: the
    coherence of the action across different orbits.
  - Periodic orbits are excluded from item 3. Periodic-point sums were killed separately (w16).
- **Caveat.** For infinite `I`, item 1 does not extend to all of `W_r`. The flux map to
  `ℓ^∞(I, Z)` gives unbounded ones. Choose an additive `h: ℓ^∞(I, Z) → R` that is unbounded on
  `{0,1}^I`, using a Hamel basis over `Q`. This is possible because indicators of disjoint subsets
  are linearly independent. Then `|h ∘ φ|²` is cnd and is unbounded on `W_1`, since `σ` applied on
  a chosen set of fibres realises any flux vector in `{0,1}^I`. On `[[X]]` the flux is constant, so
  this does not matter there.
