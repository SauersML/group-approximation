---
rg: 2
id: several-ascending-letters-reduce-to-amalgams-over-the-base
kind: claim
title: A multiple ascending HNN extension is an amalgam of single-letter extensions over the base; inner automorphism letters are centralizer extensions; the common-hat host for k ≥ 2 letters has a Cantor singular locus
distinct_from:
  germ-host-class-closed-under-sectioned-ascending-hnns: that closes 𝓒_d under one ascending letter at a time (one new singular point); this records what changes for k ≥ 2 simultaneous letters, and why that closure does not follow.
  bartholdi-multi-substitution-hnn-surjects-onto-free-group: that shows the k-letter fp overgroup maps onto F_k; this gives its structure (an amalgam over the base) and the BH reduction.
requires:
  - germ-host-class-closed-under-sectioned-ascending-hnns
---

**Status.** Parts 1 and 2 are **ESTABLISHED** (elementary, proofs below). Part 3 is a
structural observation about the natural construction, not a theorem about all hosts.
Closure of `𝓒_d` under several simultaneous ascending letters is **OPEN**.

## Setting

`K` is a group and `φ_1, …, φ_k: K → K` are injective endomorphisms. Let

```text
Ĝ = ⟨K, t_1, …, t_k | t_i^{-1} g t_i = φ_i(g)  (g ∈ K, i ≤ k)⟩
```

be the graph of groups with one vertex `K` and `k` ascending loops (Bartholdi's `Ĝ`).

## 1. Ĝ is an amalgam over the base

`Ĝ ≅ G_1 *_K G_2 *_K ⋯ *_K G_k`, with `G_i = K*_{φ_i}`: the colimit of the `G_i` along their
common subgroup `K`. The two presentations agree generator for generator: `K` together with
the letters `t_i`, and the relations of each `G_i`. So BH for `Ĝ` is BH for an amalgam of
`k` single-letter extensions over one base. Each single-letter extension is in the `𝓒`-closure
under the hypotheses of `germ-host-class-closed-under-sectioned-ascending-hnns`.

## 2. Inner automorphism letters are centralizer extensions

Let `K ≤ P`, `c ∈ P` with `cKc^{-1} = K`, and `χ(g) = c^{-1}gc` on `K`. Then

```text
⟨P, u | u^{-1}gu = χ(g), g ∈ K⟩  ≅  ⟨P, v | [v, g] = 1, g ∈ K⟩,      u ↦ cv,  v ↦ c^{-1}u.
```

**Proof.**
- **Forward map.** `(cv)^{-1}g(cv) = v^{-1}χ(g)v = χ(g)`, because `χ(g) ∈ K` commutes with `v`.
- **Backward map.** For `g ∈ K`, put `g' = cgc^{-1} ∈ K`. Then
  `(c^{-1}u)^{-1}g(c^{-1}u) = u^{-1}g'u = χ(g') = g`.
- The two maps are mutually inverse on generators. ∎

So automorphism letters realized by conjugation inside a host give `P *_K (K × F_m)`: `P`
amalgamated with a free centralizer extension of the base.

## 3. The common-hat construction for k ≥ 2 letters

Suppose all `φ_i` are cone-sectioned at the letter `L`, and we look for one hat `ĝ` per
`g ∈ K` and ray shifts `s_i` with `s_i ĝ s_i^{-1} = \widehat{φ_i(g)}`, as in the one-letter
embedding lemma.
- **Main cone.** On `LC` this forces `s_i(Lu) = LLu` for every `i`.
- **Slot data.** On `C∖LC`, the `E`-part of `ĝ` must carry the whole tail tree
  `(ψ_i φ_w(g))_{i ≤ k, w ∈ [k]^*}`, on regions `R_{i,w}` with `s_j^{-1}(R_{i,w}) = R_{i,wj}`.
  This follows by the same bookkeeping as for `k = 1`: `ψ_i` is the off-cone part of `φ_i`,
  and `φ_{wj} = φ_w∘φ_j`.
- **Singular locus.** These regions accumulate on the limit set of the free semigroup
  `⟨s_1^{-1}, …, s_k^{-1}⟩`. For `k ≥ 2` that is a Cantor set `Λ ≅ [k]^N`, not a point.

So the hats are singular along `Λ`. The host is then not a finite germ extension of the base,
and neither BHM's theorem nor its Appendix A induction applies. For `k = 1`, `Λ` is one point,
recovering the one-orbit theorem.

## Test case: Bartholdi's three-letter Fabrykowski–Gupta group

`Ĝ_Γ = Γ*_σ *_Γ (Γ ⋊_{χ_1} Z) *_Γ (Γ ⋊_{χ_2} Z)` by part 1. The letters `χ_1, χ_2` are
automorphisms. If each is induced by conjugation by some `c_i` normalizing the image of `Γ` in
a host `P ⊇ Γ*_σ`, part 2 turns BH for `Ĝ_Γ` into BH for `P *_Γ (Γ × F_2)`.

In the standard ternary action (`a` the rooted 3-cycle, `r = (a, 1, r)`), `χ_2` (`a ↦ a^{-1}`,
`r ↦ r`) is **not induced by any tree automorphism**. Write `c = (c_0, c_1, c_2)p`.
- **Root permutation.** It must invert `a`, so `p` is a reflection.
- **Sections of `crc^{-1}`.** They are `c_j r|_j c_j^{-1}` at `p(j)`. Matching `(a, 1, r)` forces
  `p(1) = 1`, so `p` swaps `0` and `2`.
- **Contradiction.** Then `c_0 a c_0^{-1} = r`. But `a` moves the root's children and `r` does
  not, so they are not conjugate.

By Lavreniuk–Nekrashevych rigidity (cited), `χ_2` is induced by a boundary homeomorphism, but
that homeomorphism is not a tree automorphism. So BH for `Ĝ_Γ` stays **open** here.

## Lesson for general BH

- **One letter vs several.** One ascending letter costs one singular point; `k` independent
  letters cost a Cantor set, the boundary of the free monoid of stable letters.
- **A two-dimensional host.** The natural k-letter host is a germ extension along a
  Cuntz-type locus: a `V_k`-like groupoid transverse to the base, as in Brin–Thompson `2V`
  structures. The germ theory there is `V_d`-type along the base and `V_k`-type along `Λ`.
- **The general program.** Closing `𝓒` under graphs of groups with ascending edges needs an
  `F_∞` criterion for such product-type singular loci. Separately, BH for amalgams over the
  base group, and for centralizer extensions `P *_K (K × F_m)`, are the two general closure
  properties this reduction asks for.
