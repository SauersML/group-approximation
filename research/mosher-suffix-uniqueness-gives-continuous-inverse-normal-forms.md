---
rg: 2
id: mosher-suffix-uniqueness-gives-continuous-inverse-normal-forms
kind: claim
title: An automatic structure with Mosher's suffix uniqueness property is suffix-continuous under right multiplication, so its inverted language is a continuous normal form for the left action
distinct_from:
  continuity-of-automatic-structures-is-decidable: that decides continuity of a given structure in the BBCMP left convention; this produces continuity from a structural property that Mosher proved for his mapping class groupoid normal forms.
  once-punctured-mcgs-are-continuous-asynchronous-automatic: that is the application to once-punctured mapping class groups; this is the general lemma.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed). Proof:
`mosher-suffix-uniqueness-continuity-proof`.

## Setting

- **Suffix uniqueness** (Mosher, *A user's guide to the mapping class group:
  once punctured surfaces*, arXiv:math/9409209, §IV, read from the TeX). Let `G` be a
  group or groupoid with finite generating set `𝒜`, and `𝓛` a synchronous or asynchronous
  automatic structure in the standard right-multiplication convention, with fellow
  traveller constant `K`. `𝓛` has **suffix uniqueness** if:
  - it is prefix closed, and no two normal forms represent the same element;
  - there are `n ≥ 1`, a finite set `𝒮 ⊂ {}_n𝓛 × B_K` and a function
    `F : 𝒮 → {}_k𝓛` with the property quoted verbatim below.

  Here `{}_n𝓛` is the set of suffixes, of length between 1 and `n`, of words of `𝓛`.
  `B_K` is the set of elements represented by words of length at most `K`.

  > If `w,w' ∈ 𝓛` are `K`-fellow travellers, then setting `g = w̄^{-1} w' ∈ B_K`, there
  > exists a unique suffix `s` of `w` such that `(s,g) ∈ 𝒮`, and `F(s,g)` is a suffix
  > of `w'`. Moreover, writing `w = ŵ s` and `w' = ŵ' F(s,g)`, then `ŵ` and `ŵ'` are
  > `K`-fellow travellers.
- **Suffix-continuity.** For `v ∈ 𝓛` and `a ∈ 𝒜`, write `v·a` for the normal form of
  `v̄ a`, when it is defined.

## Statement

1. **Suffix-continuity.** For every `a ∈ 𝒜` and every `N` there is `M = n(N+1)`
   such that: if `v, w ∈ 𝓛` have the same last `M` letters, and `v·a` and `w·a` are
   defined, then `v·a` and `w·a` have the same last `N` letters.
2. **Right multiplication is a backward transducer.** The map `v ↦ v·a` is computed by
   reading `v` from its end. The machine carries a state `g ∈ B_K`, starting at `g = a`,
   and a buffer of at most `n` letters. At each step it removes the unique admissible
   suffix `s`, emits `F(s, g)` and updates `g` to `s̄ g F(s,g)^{-1}`, the class of
   `s̄ · g · (F(s,g))^{-1}`. Finally it emits the bounded normal form of the last `g`.
3. **The inverted language (group case).** Let `G` be a group, with `𝒜` a finite
   symmetric set of group elements. Put `inv(x_1 ⋯ x_m) = x_m^{-1} ⋯ x_1^{-1}` and
   `𝓛^{inv} = {inv(v) : v ∈ 𝓛}`. Then:
   - `𝓛^{inv}` is a regular language of normal forms, and it is continuous for the left
     action, in the sense of Belk--Bleak--Chatterji--Matucci--Perego (BBCMP)
     Proposition 2.1;
   - its left multiplier relations are the reversals of the right multiplier relations
     of `𝓛`. By item 2 they are deterministic rational: read the reversed input chunk by
     chunk and check the reversed output. So `𝓛^{inv}` is a continuous asynchronous
     automatic structure in the BBCMP convention.

## Scope

- **Synchronous case.** If `𝓛` is synchronous, then the reversals of its multiplier
  relations have bounded length difference, and they are synchronous rational. In that
  case `𝓛^{inv}` is continuous automatic in the synchronous sense.
- **What BBCMP definitions were used.** For "deterministic rational" this uses the
  standard notion: a deterministic two-tape acceptor that may read either tape, with
  end markers. BBCMP §4.1 was not read, so their exact definition is not matched line by
  line.
