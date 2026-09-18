---
rg: 2
id: thompson-f-co-amenable-hosts-have-integral-end-germs
kind: claim
title: A null-set-preserving group of line homeomorphisms that contains Thurston's F and has one non-integral affine germ at an end does not contain F (or any subgroup of F) co-amenably
distinct_from:
  thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts: that kills four named hosts (T, V, the Lodha-Moore group G_0, Monod's countable H(A)); this kills every overgroup of Thurston's F in Homeo(R), countable or not, that preserves Lebesgue null sets and has one element whose germ at +infinity or -infinity is a non-integral affine map. That includes <t+1/2, b>, which the other claim lists as not covered, and Monod's full group H.
  thompson-f-co-amenable-circle-hosts-reduce-to-line-hosts: that reduces circle hosts, under every embedding of F, to line hosts and gap hosts; this kills a whole class of line hosts for the Thurston embedding.
  co-amenable-subgroups-transfer-hyperfinite-orbit-relations: that is the general transfer lemma used here; this supplies the non-hyperfinite relation (Farey germs, a Shimizu iteration, Carriere-Ghys) and a countable reduction that lets it apply to uncountable hosts.
  thompson-f-interval-orbit-relation-is-hyperfinite: that is the hyperfiniteness of F's own relation, used here as an input; this is about overgroups of F.
artifacts:
  - research/co-amenable-subgroups-transfer-hyperfinite-orbit-relations.md
  - research/thompson-f-interval-orbit-relation-is-hyperfinite.md
---

**ESTABLISHED.** Use Thurston's model of Thompson's group:
- `a(t) = t + 1`;
- `b(t)` is `t` on `t ≤ 0`, `t/(1−t)` on `[0,1/2]`, `3 − 1/t` on `[1/2,1]`, and `t + 1` on
  `t ≥ 1`;
- `F = ⟨a, b⟩ ≤ Homeo_+(R)`, the group of `C^1` piecewise-`PSL_2(Z)` homeomorphisms of `R`
  (Lodha–Moore, arXiv:1308.4250, `vN_fp.tex` l.132–134, l.271–272).

**1. Orbits of `F` off the rationals.** For every irrational `x` and every `γ ∈ PSL_2(Z)`
there is `f ∈ F` with `f = γ` on a neighbourhood of `x`. So the `F`-orbits in `R \ Q` are
exactly the `PSL_2(Z)`-orbits.

**2. Main theorem.** Let `G ≤ Homeo(R)` be a group of any cardinality. Assume:
- every element of `G` maps Lebesgue-null sets to Lebesgue-null sets;
- `F ≤ G`;
- some `g ∈ G` agrees, on a half-line `[R, ∞)` or `(−∞, R]`, with an affine map
  `s(t) = αt + β` with `α > 0`, where `s` is not an integer translation (`α ≠ 1` or
  `β ∉ Z`).

Then no countable subgroup `L ≤ G` whose Lebesgue orbit relation on `R` is hyperfinite is
co-amenable in `G`. In particular:
- no subgroup of `F` (for example `F` itself, `F'`, or any finite-index subgroup of `F`) is
  co-amenable in `G`;
- `G` is non-amenable (take `L = 1`).

**3. The invariant: germs at the ends.** Every element of Monod's group `H` (piecewise
projective homeomorphisms of `P^1` that fix `∞`) is affine near `+∞` and near `−∞`. So `H`
has two end-germ homomorphisms `∂_±: H → Aff_+(R)`. For every `G` with `F ≤ G ≤ H`:

> if `F` (or any subgroup of `F`) is co-amenable in `G`, then `∂_+(G)` and `∂_-(G)` consist of
> integer translations.

**Hosts killed** (each contains `F` and a non-integral affine germ at an end):
- `⟨t ↦ t + 1/2, b⟩`, which contains `a = (t + 1/2)^2`. Lodha–Moore l.136–138 assert without
  proof that this group is non-amenable; part 2 proves it, and it has no free subgroups
  because it lies in `H` (l.96).
- `⟨F, S⟩` for any countable set `S` of affine maps that are not all integer translations, for
  example `⟨F, 2t⟩`, `⟨F, t + 1/n⟩` and `⟨F, t + √2⟩`.
- Monod's `H` itself.
- Monod's `H(A)` for every ring `A ≠ Z` with `F ≤ H(A)`, since `t ↦ t + x` lies in `H(A)` for
  `x ∈ A \ Z`. This recovers case 4 of the heretic claim.
- Every overgroup of any of these that still preserves Lebesgue null sets.

**Where every member dies.** The Lebesgue orbit relation of `G` contains, on a conull set,
the relation of `Λ = ⟨PSL_2(Z), s⟩`. `Λ` is non-discrete by a Shimizu iteration, hence dense
by a Lie-algebra argument, hence has a non-amenable relation (Carrière–Ghys, verbatim in
Lodha–Moore l.304–306). The transfer lemma
`co-amenable-subgroups-transfer-hyperfinite-orbit-relations` would instead push the
hyperfinite relation of `F` up to `G`. The step that fails is the germ at infinity: the
translation `a` drags every point into the half-line where `g = s`, and `g a g^{-1}` is the
translation by `α` there.

**Survivors inside `H`.** The hosts left are subgroups `F ≤ G ≤ H` whose end germs are all
integral. All their non-`PSL_2(Z)` pieces are then interior, as for the Lodha–Moore group
`G_0` (killed separately by the heretic's explicit words). For an interior piece `λ` on an
interval `I`, the pseudogroup argument only yields `λγ` for `γ ∈ PSL_2(Z)` with `γx ∈ I`.
It does not yield `λ` itself, and the method stalls there.

Proof route: `thompson-f-co-amenable-hosts-have-integral-end-germs-proof`.
