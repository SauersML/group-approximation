---
rg: 2
id: perron-weights-do-not-give-li-finiteness
kind: claim
title: Li's F_n machinery needs merge packing, not a Perron height; the free-group reduced-word coding has Perron weights yet infinitely many non-simply-connected Witzel complexes, so the Perron substitution proof fails and the real gate is packing
invalidates:
  - perron-substitution-finiteness-proof
distinct_from:
  perron-substitution-finiteness-for-garside-full-groups: that claims a Perron weight can replace Li's (t<d); this shows the replacement proof breaks, gives a counterexample to its key step, and states the condition Li's proof really needs.
  raag-cube-codings-fail-li-multiplicity-at-every-power: that shows (t<d) fails for RAAG cube codings; this shows that dropping (t<d) in favour of a spectral height cannot work, because the missing ingredient is merge packing, which no height supplies.
---

**ESTABLISHED** through `perron-weights-do-not-give-li-finiteness-proof` (lane proof;
X. Li, arXiv:2110.04505v2, §`s:Fn`, read at source in
`$GQ/src/kep/li-garside-II-2110.04505v2.tex`; not independently reviewed; no priority
claimed).

## Statement

Work in Li's setting for `thm:Fn` (finitely aligned left cancellative `𝔠`, Garside family
`𝔖`, closed invariant `X ⊆ Ω_∞`, types `𝔛`, generators `Γ`, component `𝐗(*)`). Li's
packing number of an object `𝐔` is

  `ρ'(𝐔) = max { Σ_γ ρ_γ : Σ_γ ρ_γ 𝟙_{𝔛(𝐝(γ))} ≤ 𝐦_𝐔 }`,

the largest number of generator codomain patterns that fit disjointly into `𝐔`, and
`ρ(x) = max ρ'(𝐔)` over the `𝐔` unit-isomorphic to `x`.

1. **Counterexample to the Perron step.** Take `F_k` (`k ≥ 2`) with its reduced-word
   path category, which is the pointed-cube category of the `2k`-valent tree. Let `𝔛` be
   the cone types and `Γ` the one-layer expansions. This datum satisfies every hypothesis
   of Li's `thm:Fn` except (`t<d`), and it has the Perron weight (`λ = 2k − 1`).
   Nevertheless `𝐗(*)` contains pairwise non-isomorphic objects `x_N` (`N ≥ 3`) whose
   complexes `|E(x_N)|` are not simply connected.
   - So Witzel's criterion (Li's `thm:Wit`) cannot certify `F_2` for this datum with
     **any** height function.
   - So `perron-substitution-finiteness-proof` is invalid.
2. **Where the proof breaks.** Li's `lem:link:n-conn_3` (l.1729) assumes `ρ'(x) ≥ R`,
   not a large height. In Li the height *is* built from `ρ'`, so a large height gives a
   large packing for free. The Perron weight `ρ_w` has no such link: along `x_N` we have
   `ρ_w(x_N) → ∞` while `ρ'(x_N) ≤ 2`.
   - The Perron theorem is therefore **unproved** for `n ≥ 2`.
   - Its free-group instance is still true: Li's `cor:ProdGraphs` (l.2151) covers
     irreducible one-sided SFT groupoids, after Matui's recoding to at least two loops
     per vertex ([Mat15, §6.5], as Li quotes it).
   - So only the proof is refuted, and the no-recoding claim of
     `perron-recovers-free-group-boundary-full-groups` fails with it.
3. **What Li's proof actually gives (repair).** Assume Li's hypotheses for `thm:Fn`
   without (`t<d`), plus:
   - **any** height function on `𝐗(*)` with finite sublevels (a Perron weight is one;
     so is the piece count, whenever every non-unit generator has at least two nonempty
     pieces);
   - **(Pack):** for every `R`, only finitely many unit-classes `x ∈ 𝐗(*)` have
     `ρ(x) < R`.

   Then `𝒬(*,*)` is of type `F_n` whenever every `𝔠*(𝔳,𝔳)` is. Li's (`t<d`) is exactly
   the condition that makes `ρ` itself a height function, which is why it yields (Pack).
   (Pack) is strictly weaker than (`t<d`): the graph `u → u, w`, `w → w, w` fails
   (`t<d`) at `u` but satisfies (Pack).
4. **Thin cycles kill packing.** Let `R ⊆ 𝔛(*)` be a unit-invariant set of types such
   that:
   - (i) every generator in `Γ` has a codomain piece with type in `R`;
   - (ii) some cycle of generators, starting from a type in `R` that occurs in `𝐗(*)`,
     has exactly one `R`-type piece in each codomain, namely the next domain of the
     cycle, and at least one codomain in the cycle has a further piece.

   Then (Pack) fails. This is a finite check on the type graph. For `F_k` it holds with
   `R` the cone types of `a^{±1}` and the cycle "expand `a`".
5. **Consequence for cubulated groups (BBCMP Q1.15).** For Li's route, the gate is not
   (`t<d`) and not a Perron eigenvalue. It is **(Pack) for some groupoid-preserving
   presentation** of the boundary groupoid of `C_X`.
   - The untouched pointed-cube coding already fails (Pack) on trees, by item 4.
   - For graphs, the needed recoding is Matui's.
   - For pointed-cube categories, no recoding with (Pack) is known outside products of
     trees. Power families fail at (`2_Γ`) (`raag-cube-codings-fail-li-multiplicity-at-every-power`),
     and grading-free powers lose disjoint mcms (`pointed-cube-categories-are-li-garside-categories`).

## Lesson for general BH

A finiteness certificate for a full group has two halves:
- a **height** (every refinement goes up, with finitely many objects below each level);
- **merge abundance** (objects far from the base contain many disjoint patterns that
  can be merged back).

Heights are cheap: piece counts and Perron weights both work. Every real difficulty sits in
merge abundance. It fails exactly along **thin cycles**, where refining one rare piece
repeatedly produces many pieces that can only be merged back through that rare piece.
Li's (`t<d`) is a local guarantee against thin cycles. A spectral condition on the
substitution matrix cannot give one, because it counts pieces, not mergeable patterns.

So every host built from a deterministic coding (free groups, RAAGs, cube complexes,
automata) must first be recoded to remove its thin cycles, as Matui's state splitting does
for graphs. The open problem for higher-rank hosts, including Q1.15, is therefore a
**thin-cycle-free recoding that keeps lcms**. A better eigenvalue is not the missing
piece.

## Attempts

1. **(bh-major-cube-b, 2026-09-18) Item 3 is conditional.** The repaired criterion (a height
   plus (Pack)) runs Li's `lem:link:n-conn_3` as stated. Referee bh-ref-q115-a found that Li's
   written proof of that lemma asserts its key element `θ` without argument
   (arXiv:2110.04505v2, l.1733–1759). So item 3 holds only if that step can be supplied, and
   in general this is not checked.
   - Items 1–2 are unaffected: the counterexample and the location of the Perron proof's
     failure.
   - For pure-hole Cuntz data the needed instance is proved directly, by Dickson's lemma
     and doubling (Lemma L of `cuntz-stabilized-garside-full-groups-f-infinity-proof`). That
     is why `cuntz-stabilized-garside-full-groups-are-f-infinity` no longer uses item 3.
