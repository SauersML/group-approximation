---
rg: 2
id: nonamenable-almost-malnormal-subgroups-are-not-co-amenable-proof
kind: route
title: Split l^2(G/H) into the base point and its complement; the complement is a sum of quasi-regular representations of H over amenable stabilizers, so the Kesten gap confines almost invariant vectors to the base point, which an element outside H moves by root 2
target: nonamenable-almost-malnormal-subgroups-are-not-co-amenable
requires:
  - kesten-amenable-stabilizer-uniform-gap
---

Notation as in the target. `G` acts on `ℓ²(G/H)` by left translation of cosets; write `o = H`
for the base coset and `δ_o` for its indicator.

**Step 1 (a finitely generated nonamenable core).** A countable nonamenable group has a finitely
generated nonamenable subgroup (a directed union of amenable groups is amenable). Fix such
`H_0 ≤ H` with a finite symmetric generating set `S`. By `kesten-amenable-stabilizer-uniform-gap`
applied to `A = H_0`, there is `κ = κ(H_0, S) > 0` such that for every amenable `L ≤ H_0` and
every real `f ∈ ℓ²(H_0/L)`,
`Σ_{s ∈ S} ||f - s f||² ≥ κ ||f||²`. The operators `s` are real permutation operators, so
applying this to real and imaginary parts gives the same inequality for complex `f`.

**Step 2 (stabilizers off the base point are amenable).** Let `Ω = G/H \ {o}`. It is
`H`-invariant, since `h·o = o`. For `xH ∈ Ω` (so `x ∉ H`) the stabilizer of `xH` in `H_0` is
`H_0 ∩ xHx^{-1} ≤ H ∩ xHx^{-1}`, which is amenable by hypothesis (subgroups of amenable groups
are amenable). Each `H_0`-orbit in `Ω` is `H_0`-equivariantly the coset space `H_0/L` of such a
stabilizer `L`. So `ℓ²(Ω)` is the orthogonal sum of the `ℓ²` spaces of these orbits, each
`S`-invariant, and summing Step 1 over orbits gives, for every `η ∈ ℓ²(Ω)`,

```text
Σ_{s in S} || s η - η ||²  >=  κ || η ||².                                  (P1)
```

**Step 3 (the base point is moved).** Let `ξ` be a unit vector and write `ξ = a δ_o + η` with
`a = ⟨ξ, δ_o⟩` and `η ∈ ℓ²(Ω)`, so `|a|² + ||η||² = 1`. Suppose that for some `ε > 0`,
`||s ξ - ξ|| ≤ ε` for all `s ∈ S`, and `||g ξ - ξ|| ≤ ε` for one `g ∈ G \ H`.
- Since `s δ_o = δ_o` for `s ∈ S ⊂ H`, we get `s ξ - ξ = s η - η`. By (P1),
  `κ ||η||² ≤ |S| ε²`, so `||η|| ≤ δ := ε (|S|/κ)^{1/2}`.
- `g ξ - ξ = a (δ_{gH} - δ_o) + (g η - η)`, and `gH ≠ o`, so
  `||g ξ - ξ|| ≥ √2 |a| - 2 ||η||`. Hence `√2 |a| ≤ ε + 2δ`.

Take `ε ≤ c := min(1/4, (1/4)(κ/|S|)^{1/2})`. Then `δ ≤ 1/4`, so
`|a| ≥ (1 - 1/16)^{1/2} > 0.96`, while `√2 |a| ≤ 1/4 + 1/2 = 3/4` forces `|a| < 0.54`. This is a
contradiction. So for every unit `ξ` and every `g ∉ H`, one of the vectors `s ξ - ξ` (`s ∈ S`) or
`g ξ - ξ` has norm greater than `c`, which is (AM1). Since `H ≠ G`, such a `g` exists, and
`ℓ²(G/H)` has no almost invariant unit vectors.

**Step 4 (co-amenability and inheritance).** By Eymard's equivalence (standard; the same
equivalence is used in `thompson-t-co-amenable-subgroup-kills-real-euler-class` and
`thompson-t-euler-splitting-from-co-amenable-subgroup`), `G/H` has a `G`-invariant mean iff
`ℓ²(G/H)` has almost invariant unit vectors. So `H` is not co-amenable.
- If `K ≤ H` and `m` were a `G`-invariant mean on `G/K`, its push-forward under the
  `G`-equivariant map `G/K → G/H`, `gK ↦ gH`, would be a `G`-invariant mean on `G/H`. So `K`
  is not co-amenable.
- For `t ∈ G`, the map `gH ↦ g t^{-1} · tHt^{-1}` is a `G`-equivariant bijection
  `G/H → G/(tHt^{-1})`, so `tHt^{-1}` and all its subgroups are not co-amenable either. ∎

**Calibration.** Both hypotheses are used.
- Nonamenability of `H`: the trivial subgroup of an infinite amenable group is malnormal and
  co-amenable. The proof fails at Step 1, where there is no Kesten gap.
- Amenable self-intersections: a normal subgroup `H` of infinite index with `G/H` amenable is
  co-amenable. The proof fails at Step 2, since then `H` fixes every point of `Ω`.
