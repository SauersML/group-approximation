---
rg: 2
id: cover-pair-sections-pull-back-along-retraction-data
kind: claim
title: Sections of cover pairs pull back along retraction data, so inducing a section-less cover pair to any supergroup or product never creates a section, while finite-index restriction genuinely relaxes the section condition
distinct_from:
  cover-pair-sections-force-fixed-point-surjectivity: that pulls back deficiencies D_H along morphisms of pairs over one group; this pulls back sections themselves across a change of group, so it also kills host changes for nondeficient section-less pairs, which F2 there does not reach.
  cover-pair-sections-localize-to-the-symmetric-locus: that localizes the section problem at one group to seeds exact on Sym_E; this shows the problem cannot be moved to a larger host, and names the one host change (finite-index restriction) that shrinks Sym_E.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is the target statement; this closes one family of attacks on its converse gap (need 06d50d0e) and does not decide it.
artifacts:
  - research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md
---

**ESTABLISHED (unreviewed)** by [[cover-pair-sections-pull-back-along-retraction-data-proof]]. Elementary.

**Setting.** A *cover pair* `(X, F)` at a group `G` over `A` is as in
`post-surjective-sft-covers-admit-scheduled-sections`: `X ⊊ A^G` an SFT, `F : X → A^G` an automaton, strongly
post-surjective with lifts in `X`. A *section* is a continuous `G`-equivariant `s : A^G → X` with `F ∘ s = id`.
Action: `(g.x)(h) = x(g^-1 h)`.

Let `G ≤ G'` and let `(X', F')` be a cover pair at `G'` over `A'`. A **retraction datum** from `(X', F')` to
`(X, F)` is a triple of continuous `G`-equivariant maps

```text
ι : A^G → A'^(G'),   π : A'^(G') → A^G,   β : X' → X,   with   π ∘ ι = id   and   F ∘ β = π ∘ F'.
```

**T1 (pull-back).** If `(X', F')` has a section `s'` (even one that is only `G`-equivariant), then
`s = β ∘ s' ∘ ι` is a section of `(X, F)`.

**T2 (induction).** For every supergroup `G' ≥ G` the induced pair `Ind(X, F)` (read `X` on every left coset
`g'G`, apply `F` cosetwise) is a cover pair at `G'` with a constant point, and it has a section iff `(X, F)` has
one. The same holds for `Ind(X, F) × (Y, F_Y)` with any cover pair `(Y, F_Y)` at `G'`, and after any recoding.
This covers `G × K`, `G * K`, amalgams, HNN extensions, wreath products and every other overgroup.

**T3 (finite-index relaxation).** Let `H ≤ G` have finite index. If some cover pair at `G` has a continuous
`H`-equivariant section, then `G` is not surjunctive. So in Proposition C, and in need 06d50d0e, `G`-equivariance
may be weakened to `H`-equivariance for any finite-index `H`. The symmetric locus shrinks to the fixed sets of
elements of `H`.

**What it kills.** The class of attacks on `Gottschalk ⇒ CP` (need 06d50d0e) that move a constant-point cover
pair to a better host group to find room for a section. Invariant: existence of a section, which T1 pulls back.
Dying step: if `G` is surjunctive, a CP counterexample `(X, F)` has no section (Proposition C). So by T1 no
transport with a retraction datum has a section, even when the new host `G'` is non-surjunctive. A non-surjunctivity
witness at `G'` built from `(X, F)` must break `G`-equivariance of `ι`, `π` or `β`.

**What survives.** Only host changes without a `G`-equivariant retraction. T3 is one of them: it keeps the pair,
weakens equivariance to finite-index `H`, and removes `Fix(e)` for `e ∈ G \ H` from the obstruction. It does not
remove constants, so `D = ∅` is still needed. It is empty for groups with no proper finite-index subgroup.
