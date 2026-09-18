---
rg: 2
id: af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan
kind: claim
title: "The Robertson–Steger boundary groupoid Γ⋉Ω of a Kazhdan PGL_3 lattice is minimal, effective (the action is topologically free), Hausdorff, ample, amenable and expansive, and carries a continuous Z^2 cocycle with AF kernel; so AF-by-Z^k for k ≥ 2 does not force Kazhdan subgroups of the full group to be finite"
distinct_from:
  rs-boundary-groupoid-is-expansive-amenable-kazhdan-host: that proves the same groupoid is expansive, minimal and amenable, with Γ in its full group, and explicitly does not assert effectiveness; this proves effectiveness (topological freeness of Γ ↷ Ω) and constructs a continuous Z^2 cocycle with AF kernel, the two properties that host lacked for the AF-by-Z^k question.
  rank-two-prefix-replacement-groups-contain-infinite-kazhdan: that shows Γ acts by prefix replacements with Z^2 shape offsets, but never shows the offset is a well defined function of the arrow; this proves it is, via the gauge action, and that its kernel is an AF groupoid.
  a2-group-embeds-in-full-group-of-its-rs-two-graph: that asks for Γ inside the full group of the Kumjian–Pask groupoid through Renault reconstruction, with unpinned imports; this works on Γ⋉Ω itself and needs no identification with the 2-graph groupoid (it does supply the topological freeness that node's step 3 assumes).
  expansive-amenable-purely-infinite-groupoid-hosts-kazhdan: that host (M⋊Γ)×G_2 has a degree cocycle whose kernel contains Γ and leaves open whether some other cocycle has an AF kernel; this host has a Z^2 cocycle with AF kernel.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that host is effective and amenable but its natural cocycle has a non-AF kernel and it is not known to be expansive; this host has all three properties together with an AF-kernel Z^2 cocycle.
---

**ESTABLISHED** through `af-by-z2-kazhdan-host-proof`.

## Setting

As in `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`:
- `K` is a nonarchimedean local field of characteristic zero, and `B` is the building of
  `PGL_3(K)` with boundary `Ω` and base vertex `O`.
- `Γ` is a lattice in `PGL_3(K)` acting on `B` type rotatingly, freely on vertices, with
  finitely many vertex orbits. Robertson–Steger record concrete examples
  (`robertson-steger-boundary-cylinders-and-pure-infiniteness`, item 7).
- `R = Γ ⋉ Ω` is the transformation groupoid, the set `Γ × Ω` with the product topology,
  `s(γ,ω) = ω`, `r(γ,ω) = γω`, and `(δ,γω)(γ,ω) = (δγ,ω)`.

**Definitions used.**
- A *continuous `Z^k` cocycle* is a continuous groupoid homomorphism `c: R → Z^k`.
- `R` is *effective* if the interior of `Iso(R) \ R^{(0)}` is empty. It is *topologically
  principal* if the units with trivial isotropy are dense.
- An étale groupoid `H` with compact unit space is *AF* if `H = ⋃_N K_N` for an increasing
  sequence of compact open principal subgroupoids `K_N` with `K_N^{(0)} = H^{(0)}`. This is
  Matui's definition of an AF groupoid, and the one in the need `(S_k)` below.

## Statement

1. **Standing properties** (from `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`).
   - `R` is second countable, Hausdorff and ample, with Cantor unit space.
   - It is minimal, compactly generated and expansive.
   - It is the groupoid of an amenable action.
   - Its unit space carries no invariant probability measure.
   - `Γ` is infinite, finitely generated and Kazhdan, and `γ ↦ {γ} × Ω` embeds `Γ` in `[[R]]`.
2. **Topologically free.** For every `γ ≠ 1`, the fixed set `{ω : γω = ω}` has empty
   interior. Hence `R` is effective and topologically principal, and `R` equals the
   groupoid of germs of `Γ ↷ Ω`.
3. **The Z² cocycle.** There is a unique function `c: R → Z²` with the following property.
   Whenever `γ1_{Ω(p)} = φ(s_{ᾱ(p'),ᾱ(p)})` in `C(Ω)⋊Γ` with `ω ∈ Ω(p)`, it gives
   `c(γ,ω) = σ(p') - σ(p)`, the Robertson–Steger shape offset. This `c` is a continuous
   cocycle.
4. **AF kernel.** `ker c = {(γ,ω) : c(γ,ω) = 0}` is an AF groupoid with unit space `Ω`.
   Explicitly `ker c = ⋃_N K_{(N,N)}`, where `K_m` is the set of `(γ,ω)` such that
   `γ|_{Ω(p)}` is a same-shape prefix replacement `ᾱ(p) ⇒ ᾱ(p')` with `ω ∈ Ω(p)` and
   `p, p' ∈ 𝔚̄_m`. Each `K_m` is a compact open principal subgroupoid containing `Ω`.
5. **All ranks k ≥ 2.** For every `k ≥ 2`, `c_k = (c, 0, …, 0): R → Z^k` is a continuous
   cocycle with `ker c_k = ker c`, which is AF.

## Consequences

**(S_k) is false for every k ≥ 2.**
- The need `(S_k)` (bus need `239f5784`, posted by `e2-w2-nv-separate`, not yet a node) asks:
  "if a minimal effective ample groupoid carries a continuous `Z^k` cocycle with AF kernel,
  are all Kazhdan subgroups of its topological full group finite?"
- `R` is such a groupoid for every `k ≥ 2`, and `Γ ≤ [[R]]` is an infinite Kazhdan group.
- So the answer is **no** for every `k ≥ 2`. The one-hole route through `(S_n)` to
  `kazhdan-subgroups-of-brin-thompson-groups-are-finite` is dead for `n ≥ 2`.
- `(S_1)` is untouched. It is established for one-sided SFT groupoids, and `c` is not
  pulled back from a `Z`-valued cocycle with AF kernel: no homomorphism `Z² → Z` is
  injective.

**Class kill (calibration of nV).**
- **Killed class.** Proofs that `[[𝒢]]` has finite Kazhdan subgroups, or the Haagerup
  property, from any sublist of the following hypotheses on `𝒢`:
  - second countable, Hausdorff, étale, with Cantor unit space;
  - minimal, effective, topologically principal, essentially principal;
  - compactly generated and expansive;
  - the groupoid of an amenable action, with no invariant probability measure;
  - `C*(𝒢)` simple, nuclear and purely infinite;
  - **a continuous `Z^k` cocycle with AF kernel, for any fixed `k ≥ 2`.**
- `G_2^n` has every one of these properties for `k = n` (for the cocycle, see the need's
  source `brick-groupoid-has-zn-cocycle-with-af-kernel` on the bus).
- **Invariant:** property (T) of `Γ`.
- **Where every member dies.** At the step that turns the hypotheses into a finiteness
  conclusion, or into a proper conditionally negative definite function on `[[𝒢]]`, applied
  to `𝒢 = R`.
  - `Γ ≤ [[R]]` is infinite, so no finiteness conclusion holds.
  - A proper cnd function restricted to `Γ` would be bounded by Delorme–Guichardet (as in
    `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`), so it could not be proper.
- **Closes audit D1** of `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`: one
  Hausdorff groupoid is both expansive and effective. So the "Hausdorffness escape"
  recorded there is gone.

**What survives.**
- The *product factorization* `G_2^n = G_2 × ⋯ × G_2`, and with it the splitting of the
  AF-by-`Z^n` structure into rank-one pieces. `R` is not known to split, and its word
  system couples the two directions through the (H1) squares.
- Matui pure infiniteness of the groupoid `R` itself, which is not asserted here
  (`C*(R)` is purely infinite).
- `(S_1)`, and any hypothesis that ties the cocycle to a *product* of rank-one groupoids.

## Not asserted

- That `R` is purely infinite in Matui's groupoid sense.
- That `R` is isomorphic to, or Kakutani equivalent to, the Kumjian–Pask groupoid of the
  Robertson–Steger 2-graph. The AF kernel is built on `Γ⋉Ω` directly.
- That `Γ` embeds in any `nV`.
