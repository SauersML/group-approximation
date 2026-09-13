---
rg: 2
id: free-group-virtual-sections-give-punctured-birman-sections
kind: claim
title: A section of Aut(F_n) to Out(F_n) over a finite-index subgroup restricts to a virtual section of every punctured-surface Birman sequence of rank n
distinct_from:
  outer-covering-lifts-are-virtual-sections: that turns covering-lift constructions into virtual sections of Aut to Out; this goes the other way, restricting a virtual section of Aut(F_n) to Out(F_n) to the Dehn--Nielsen--Baer copies of punctured-surface mapping class groups.
  free-splitting-compatible-aut-lifts-are-virtual-sections: that produces sections of Aut(F_n) to Out(F_n) from homomorphisms into larger free products; this consumes such a section and produces sections of punctured-surface Birman sequences.
  birman-exact-sequence-does-not-virtually-split: that is Chen--Salter's non-splitting for closed surfaces; this is an elementary restriction lemma whose targets are Birman sequences over punctured surfaces, which that theorem does not cover.
artifacts:
  - research/artifacts/solve-bh-mcg-outfn-2026-09-13.md
---

**ESTABLISHED.** Elementary; no novelty is claimed. The derivation is
`free-group-virtual-sections-punctured-birman-proof`.

Let `g ≥ 0` and `k ≥ 1` with `n = 2g + k − 1 ≥ 2`, and let `Σ_{g,k}` be the
orientable surface of genus `g` with `k` punctures. Write `PMod` for pure,
orientation-preserving mapping class groups.

Suppose `Γ ≤ Out(F_n)` has finite index and `s: Γ → Aut(F_n)` is a homomorphism
lifting the inclusion. Identify `F_n = π1(Σ_{g,k}, ∗)` and `PMod(Σ_{g,k})` with its
Dehn--Nielsen--Baer image in `Out(F_n)`. Then `Γ_0 := Γ ∩ PMod(Σ_{g,k})` has finite
index in `PMod(Σ_{g,k})`, and `s` restricts to a homomorphism
`Γ_0 → PMod(Σ_{g,k+1})` that splits the Birman exact sequence

    1 → π1(Σ_{g,k}) → PMod(Σ_{g,k+1}) → PMod(Σ_{g,k}) → 1

over `Γ_0`. The new puncture is the base point `∗`, and the map forgets it.

**Consequence.** If the Birman sequence of `Σ_{g,k}` does not virtually split for
some `(g,k)` with `2g + k − 1 = n`, then `Aut(F_n) → Out(F_n)` does not virtually
split. Chen--Salter's theorem covers only closed surfaces
(`birman-exact-sequence-does-not-virtually-split`), so it does not apply directly.
The once-punctured case is `once-punctured-birman-sequence-does-not-virtually-split`.
