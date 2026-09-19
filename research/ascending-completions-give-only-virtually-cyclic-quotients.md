---
rg: 2
id: ascending-completions-give-only-virtually-cyclic-quotients
kind: claim
title: "Ascending-HNN-style commensurated witnesses (Sigma contracted into itself by one letter t, with F inside the ascending union of t-conjugates of Sigma extended by t) only realize virtually cyclic P = F/N, with no finiteness or torsion hypothesis; so the BS(1,2)-type construction for Z/2 wr Z (and for U, V, Grigorchuk, even Z^2) is impossible, and any witness for Z/2 wr Z needs a two-sided completion in which every lamp is neither forward- nor backward-parabolic for the shift"
distinct_from:
  f-cores-reduce-benign-witnesses-to-normalized-ones: That kills commensurated witnesses whose F-core has finite index (open closure of F), and leaves open an infinite-index core, with BS(1,2) as the sharpness example; this kills the whole ascending family generalizing that example, whose cores do have infinite index, by contraction dynamics rather than by Browder.
  commensurated-witnesses-survive-browder-but-die-when-linear: That kills completions linear over characteristic-0 local fields and locally finite trees, via bounded finite-subgroup ranks; this kills ascending completions of any kind (non-linear, characteristic p, any Sigma) and bounds P to be virtually cyclic, which also excludes torsion-free P such as Z^2.
  ascending-hnn-torsion-quotients-see-only-coinvariants: That concerns torsion quotients of ascending HNN groups themselves; this concerns quotients F/(F cap Sigma) cut out by the vertex group for arbitrary subgroups F.
  commensurated-cat0-witnesses-force-finite-rational-cd: That bounds cd_Q of P by the dimension of a CAT(0) complex, which Z/2 wr Z (cd_Q = 2) passes from dimension 2; this uses no geometry and excludes Z/2 wr Z outright in the ascending class.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Setting as in
`f-cores-reduce-benign-witnesses-to-normalized-ones`: `F` free (any group
works below), `N ⊴ F`, `P = F/N`, a witness `Σ ≤ Λ ⊇ F` with `Σ ∩ F = N`.
Nothing is assumed about finiteness type, torsion, or `cd`.

**Theorem.**

1. **Parabolic lemma (any tdlc completion).** Let `G` be a totally
   disconnected locally compact group, `K ≤ G` compact open, `ρ : F -> G`
   with `N = ρ^{-1}(K)`. Let `Ĥ` be the closure of `ρ(F)`. Then
   `M = Ĥ ∩ K` is a compact open normal subgroup of `Ĥ` and
   `Ĥ/M ≅ P`. For every `τ ∈ Ĥ`, with image `τ̄ ∈ P`, every element of
   the parabolic set `par(τ) ∩ Ĥ` (those `x` whose forward orbit
   `{τ^n x τ^{-n} : n ≥ 0}` is relatively compact) maps into
   `⋃_{d ≥ 1} C_P(τ̄^d)`. If moreover `L ≤ Ĥ` is compact open with
   `τLτ^{-1} ⊆ L`, then every `x` with `τ^n x τ^{-n} ∈ L` for large `n`
   maps into the finite group `LM/M`, and `τ̄` normalizes it.
2. **Ascending completions.** Call `G` *ascending* if it has a compact open
   `K` and an element `t` with `tKt^{-1} ⊆ K` and `G = G_0⟨t⟩`, where
   `G_0 = ⋃_{k ≥ 0} t^{-k}Kt^k`. If `G` is ascending and `N = ρ^{-1}(K')`
   for some compact open `K' ≤ G` and a homomorphism `ρ` of a finitely
   generated `F`, then `P` is **finite or finite-by-`Z`**, i.e. virtually
   cyclic.
3. **Ascending witnesses.** Suppose some `t ∈ Λ` has `tΣt^{-1} ⊆ Σ` with
   finite index, and `F ⊆ Γ = Λ_0⟨t⟩`, where
   `Λ_0 = ⋃_{k ≥ 0} t^{-k}Σt^k`. Then the Schlichting completion of
   `(Γ, Σ)` is ascending, so `P` is virtually cyclic. This covers:
   - every `F` inside an ascending HNN extension `Λ = Σ*_φ` with
     `[Σ : φ(Σ)] < ∞`, for instance `BS(1,n)`, `Z^n *_A` and
     `Σ ⋊_φ Z`;
   - every group `⟨Σ, t⟩` with `tΣt^{-1} ≤ Σ` of finite index.
4. **Consequences.** No witness of the kind in item 3 or item 2 exists for
   `P = Z/2 ≀ Z`, nor for `U`, `V`, Grigorchuk's group, `Z^2`, or any
   finitely generated group that is not virtually cyclic. This holds with
   `Λ` and `Σ` of any finiteness type, torsion-free or not. So the step
   "build a type `F` commensurated witness for `Z/2 ≀ Z` by an
   ascending-HNN-style `Σ` generalizing `BS(1,2)`" is **impossible**.
   The contraction by `t` forces the kernel of `P -> Z` to be finite.

**Sharpness.**
- `BS(1,2)` with `Σ = ⟨a⟩` and `F = ⟨t⟩` gives `P = Z`, which is
  virtually cyclic. This is the example of
  `f-cores-reduce-benign-witnesses-to-normalized-ones`.
- One contracting letter is essential. `Λ = Z[1/6] ⋊ Z^2`, with the two
  generators acting by `2` and `3`, is torsion-free of type `F`. The
  subgroup `Σ = Z` is commensurated, and `Z^2 ∩ Σ = 1`. Pull back along
  `F_2 -> Z^2`, using the witness `(Λ × F_2, Σ × F_2)` with `F_2` embedded
  diagonally. This realizes `P = Z^2`. The completion `(Q_2 × Q_3) ⋊ Z^2`
  has `G/G_0 ≅ Z^2`, so it is not ascending.

**What survives for `Z/2 ≀ Z`.** Let the completion `G` be arbitrary and
`τ ∈ Ĥ` a lift of the shift generator. By item 1, every lamp preimage
outside `M` has an unbounded forward `τ`-orbit **and** an unbounded backward
`τ`-orbit. The reason is that the centralizer of any nonzero power of the
shift in `Z/2 ≀ Z` meets the base trivially. So `τ` must act on the lamps
hyperbolically in both directions. This is exactly how `F_2[t^{±1}]` sits in
`(F_2((t)) × F_2((t^{-1}))) ⋊ Z`. Characteristic-0 linear completions are
already excluded by
`commensurated-witnesses-survive-browder-but-die-when-linear`. The remaining
test case is therefore a torsion-free type `F` pair with a **two-sided,
non-linear or characteristic-`p`** completion. One example of the shape
needed is a multi-letter ascending `Σ` whose completion carries a
characteristic-2 contraction-expansion pair.

Proof: route `ascending-completions-give-only-virtually-cyclic-quotients-proof`.

## Attempts

- 2026-09-18 (w15-117): items 1–4 proved. Proposed-established. The
  ascending-HNN construction step for `Z/2 ≀ Z` is ruled out. Open: a
  two-sided completion realizing `Z/2 ≀ Z` from a torsion-free type `F`
  pair, or an obstruction to one.
