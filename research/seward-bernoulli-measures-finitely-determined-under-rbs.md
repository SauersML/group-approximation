---
rg: 2
id: seward-bernoulli-measures-finitely-determined-under-rbs
kind: claim
title: A Bernoulli measure whose Rokhlin entropy equals its base entropy is finitely determined in the d-bar sense, over every countably infinite group
distinct_from:
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: that imports Seward's values of Bernoulli Rokhlin entropy from Krieger II; this imports the finitely determined property that his factor theorem paper derives when that value is the base entropy.
  iid-generators-not-dense-at-positive-rokhlin-supremum: that shows category arguments over i.i.d. partitions fail at positive supremum; this is the d-bar continuity of Bernoulli measures that Seward's perturbative factor theorem gives under full Bernoulli Rokhlin entropy.
---

**ESTABLISHED (import)** by [[seward-bernoulli-measures-finitely-determined-under-rbs-citation]].

Let `G` be a countably infinite group, `L` a finite set, `M_G(L^G)` the `G`-invariant Borel probability measures
on `L^G`, `h_G` Rokhlin entropy and `Stab_*(µ)` the stabilizer type of `µ`. Then:

1. **Definitions.** For `µ, ν ∈ M_G(L^G)`, `d̄(µ, ν)` is the infimum of `λ((x, y) : x(1_G) ≠ y(1_G))` over
   invariant joinings `λ` of `µ` and `ν`. `µ` is **finitely determined** if for every `ε > 0` there are a
   weak*-open `U ∋ µ` and `δ > 0` such that `d̄(µ, ν) < ε` for every `ν ∈ U` with `Stab_*(ν) = Stab_*(µ)` and
   `|h_G(L^G, ν) − h_G(L^G, µ)| < δ`.
2. **Corollary 1.6.** If `(L, λ)` is a finite probability space with `h_G(L^G, λ^G) = H(L, λ)`, then `λ^G` is
   finitely determined.

So under RBS(`G`), for instance on every sofic group and whenever INF(`G`) holds, every finite-alphabet
Bernoulli measure is finitely determined.

**Verbatim**, from arXiv:1804.05269v3 (B. Seward, *Positive entropy actions of countable groups factor onto
Bernoulli shifts*, 21 May 2019), text extracted by lane ex-bernoulli-rokhlin-complete and read on 2026-09-13:
- Section 1: "In this paper, hG will always denote Rokhlin entropy."
- Section 1, after Corollary 1.5: "for a finite set L and two G-invariant probability measures µ;ν on LG, their
  d-bar distance d̄(µ;ν) is deﬁned to be the inﬁmum of λ({(x;y) ∈ LG ×LG : x(1G) ≠ y(1G)}); where λ ranges over
  all joinings of µ with ν. The measure µ is ﬁnitely-determined if for every ǫ > 0 there is a weak∗-open
  neighborhood U of µ and δ > 0 such that whenever ν ∈ U satisﬁes Stab∗(ν) = Stab∗(µ) and
  |hG(LG;ν) − hG(LG;µ)| < δ we have d̄(µ;ν) < ǫ."
- "Corollary 1.6. Let G be a countably inﬁnite group and let (L;λ) be a ﬁnite probability space. If
  hG(LG;λG) = H(L;λ) then λG is ﬁnitely-determined."
- Section 10 restates the definition with "λ ∈ MG(KG×KG) varies over all joinings of µ with ν", so the
  joinings are invariant, and proves the IRS generalization as Theorem 10.4 from the perturbative factor
  theorem, Theorem 9.1.

Seward's acknowledgments credit Tim Austin with pointing out this consequence.
