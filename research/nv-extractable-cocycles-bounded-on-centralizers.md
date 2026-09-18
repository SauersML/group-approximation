---
rg: 2
id: nv-extractable-cocycles-bounded-on-centralizers
kind: claim
title: "Class-kill for nV: every 1-cocycle into a representation with a measure extraction in one coordinate is bounded on the centralizer of that coordinate copy of V, which contains (n-1)V; so no chart, point-orbit, quasi-regular-of-amenable or Koopman representation carries a proper cocycle, or a witness of R1, P1, P2 or P3"
distinct_from:
  nv-vertically-triangular-chart-cocycles-are-bounded: that bounds cocycles v - g.v on all of nV but only for v supported on vertically triangular charts (it needs the codimension-one sweep); this needs no support condition and covers every representation with a coordinate measure extraction, but bounds the cocycle only on the centralizer of one coordinate copy of V
  extractable-character-spectra-carry-no-almost-invariant-vectors: that uses the same three elements of V against the central element 1_C of C(C,Z) ⋊ V on character spectra; this pairs the gap with the commuting coordinate copies of V inside nV, a product structure that C(C,Z) ⋊ V does not have
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that bounds fibre elements in every commensurating action; this bounds all of (n-1)V, for every cocycle (not only cubical ones) into an extractable representation
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that kills commensurating actions via distortion of the Callard-Salo element; this kills a class of non-cubical Hilbert-space cocycles without using distortion
---

**ESTABLISHED** by `nv-extractable-cocycles-bounded-on-centralizers-proof`.

**Setting.** `C = {0,1}^ω`, `n ≥ 2`, `G = nV` acting on `C^n`. For `h ∈ V` and
`1 ≤ j ≤ n`, let `h^{(j)} ∈ G` act by `h` on coordinate `j` and by the identity on the others.
Let `h_1, h_2, h_3 ∈ V` be the elements of `nv-vertically-triangular-chart-cocycles-are-bounded`:
`h_1` is `0t ↦ 00t, 10t ↦ 01t, 11t ↦ 1t`; `h_2` is `0t ↦ 01t, 10t ↦ 00t, 11t ↦ 1t`; and
`h_3` is `it ↦ (1−i)t`. Put `β^{(j)}_i = h_i^{(j)}`, and let `Z_j` be the centralizer of
`{β^{(j)}_1, β^{(j)}_2, β^{(j)}_3}` in `G`.

`Z_j` contains `E_j`, the copy of `(n−1)V` that acts on the coordinates other than `j`
uniformly in `x_j`. In particular it contains `V_{(k)} = {h^{(k)} : h ∈ V}` for every `k ≠ j`.

**Definition.** A unitary representation `ρ` of `G` on `K` is **`j`-extractable** if there is a
map `r ↦ μ_r` from `K` to finite positive Borel measures on `C` with:
- `μ_r(C) = ‖r‖²`;
- `μ_{ρ(h^{(j)}) r} = h_* μ_r` for `h ∈ {h_1, h_2, h_3}`;
- `|μ_r(B) − μ_s(B)| ≤ ‖r − s‖(‖r‖ + ‖s‖)` for every Borel `B`.

It is **coordinate-extractable** if it is `j`-extractable for every `j`.

**Theorem.** Let `ρ` be `j`-extractable and let `b` be a 1-cocycle of `G` into `ρ`.
1. (Gap.) `‖r‖² ≤ 100 Σ_i ‖r − ρ(β^{(j)}_i) r‖²` for every `r ∈ K`.
2. (Centralizer bound.) For every `a ∈ Z_j`,

   `‖b(a)‖² ≤ 400 Σ_{i=1}^{3} ‖b(β^{(j)}_i)‖²`.

So the cnd function `ψ = ‖b‖²` is bounded on `Z_j ⊇ E_j ≅ (n−1)V`.

**Examples** (all coordinate-extractable). Here `π` is an arbitrary unitary representation
of `G` on `H`.
- *Chart modules.* `ℓ²(X; H)` for any `G`-invariant set `X` of Brin–Thompson charts
  `φ: C^n → U`, with `μ_r = Σ_φ |r(φ)|² (pr_j∘φ)_*λ`. There is no support condition: all rows,
  all orbits, all charts.
- *Quasi-regular modules.* `ℓ²(G/L) ⊗ π` for every subgroup `L` that preserves a Borel
  probability measure on `C^n`. This includes every amenable `L`, the trivial group (the regular
  representation), point stabilizers (point-orbit modules), and rigid stabilizers of clopen
  sets (chart stabilizers).
- *Koopman modules.* `L²(Ω, μ; H)` with `(ρ(g)f)(ω) = √(d g_*μ/dμ)(ω) π(g) f(g^{-1}ω)`, for
  any `G`-space `Ω` with a quasi-invariant σ-finite measure and an equivariant Borel map
  `p: Ω → Prob(C^n)`. This includes the Koopman representation on `L²(C^n, λ)` and its
  wavelet and measured-wall relatives whose walls have an equivariant location.
- *Closure.* The gap inequality (1) for a fixed `j` passes to direct sums, subrepresentations,
  unitary conjugates `ρ∘Ad(t)`, and representations weakly contained in `ρ`. Composing with a
  coordinate permutation `α_σ` moves it to the permuted coordinate.

**Corollaries.** Let `ψ = ‖b‖²` with `b` a cocycle into a representation that satisfies (1)
for some `j`. Call these the gap class.
1. *Not proper.* `ψ` is bounded on the infinite subgroup `E_j`. So no representation in the
   gap class carries a proper cocycle of `nV`, for any `n ≥ 2`.
2. *Not P3.* `E_j ∩ ker c` is infinite. It contains every level permutation `σ^{(k)}`
   (`k ≠ j`) of `Sym(2^m)` acting on cylinders of coordinate `k`. So `ψ` is not proper on the
   kernel `K` (`brin-thompson-nv-cnd-proper-on-cocycle-kernel`).
3. *Not P1.* `‖c(g)‖` is unbounded on `V_{(k)} ⊆ E_j`, for example along `(h_1^N)^{(k)}`.
   So `ψ ≥ F(‖c‖)` fails for every `F → ∞`
   (`brin-thompson-nv-exponent-cocycle-scale-is-cnd-dominated`). *Not P2* either: let
   `g_m ∈ V` act as `0^m u ↦ 0^m h_1(u)` on `[0^m]` and as the identity elsewhere. Then `c(g_m)`
   is `+1` on `[0^m 0]` and `−1` on `[0^m 11]`, so `pd(g_m^{(k)}) ≥ m + 1` while `g_m^{(k)} ∈ E_j`.
4. *Not R1.* If `ρ` satisfies (1) for every `j` (for example if `ρ` is coordinate-extractable),
   then `ψ` is not proper modulo `T_n` (`brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`),
   for every `n ≥ 2`.
   - The explicit function `Σ_{t,σ} ψ∘α_σ^{-1}∘Ad(t)` of
     `brin-thompson-nv-haagerup-iff-proper-modulo-triangular` is `‖⊕b_{σ,t}‖²` for a cocycle
     into `⊕ ρ∘α_σ^{-1}∘Ad(t)`, which again satisfies (1). So it would be proper, which
     contradicts Corollary 1.
   - For `n ≥ 3` there is also a direct argument: `E_n ⊇ (n−1)V × id` meets `T_n` in
     `T_{n−1} × id`, of infinite index.
5. *Necessary shape of a witness.* If `b` is a proper cocycle into any `ρ`, then for every `j`
   the restriction of `ρ` to `⟨β^{(j)}_1, β^{(j)}_2, β^{(j)}_3⟩` has almost invariant vectors.
   Conjugating, the same holds for every copy `t V_{(j)} t^{-1}`. So `ρ` admits no
   measure extraction in any coordinate, and no representation weakly contained in an
   extractable one does either.

**What this removes.** The survivors listed by
`nv-vertically-triangular-chart-cocycles-are-bounded` ("charts with non-triangular last
coordinate, unions of all rows, point orbits, and measure-valued or non-chart parameter
spaces", as far as the parameter space carries an equivariant map to `Prob(C^n)`) are all
coordinate-extractable. None of them yields the Haagerup property, R1, P1, P2
or P3. The dead Koopman-wavelet lane of `brin-thompson-nv-cnd-proper-on-cocycle-kernel` is
covered too, as a whole class and not only its level-weighted members.

**What this does not do.** It does not bound gap-class cocycles on all of `G`. For `ρ`
satisfying (1) in every coordinate (for example coordinate-extractable), it bounds them on
`E_1 ∪ … ∪ E_n` and on bounded products of these.
- For `n = 2` that is `V × V = V^2`.
- A gap-class cocycle on `nV` is therefore a function on the coset geometry of the
  subgroups `E_j`.
- It is unbounded only if `nV` is not boundedly generated by `E_1 ∪ … ∪ E_n` and a finite
  set. For `n = 2`, a counting heuristic suggests the baker's powers are not boundedly
  generated this way: each factor from a finite set moves boundedly many bits between the
  coordinates.
- Whether the whole gap class has bounded cocycles (which would be a relative form of
  property FH for `nV`) is OPEN.
- The class also excludes nothing about representations in which every coordinate copy of
  `V` has almost invariant vectors.
