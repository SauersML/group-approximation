---
rg: 2
id: fpbs-cs-set-family-hypothesis-fails-infinite-centre
kind: claim
title: On every Cayley graph of a group with infinite centre, the set-family hypothesis of Choi-Seo's susceptibility theorem fails for every family and every radius
distinct_from:
  fpbs-acylindrically-hyperbolic-critical-l2-gap: that imports Choi-Seo's verification of the set-family hypothesis for acylindrically hyperbolic groups and deduces p_c < p_(2->2); this proves the hypothesis is false, not just unproved, on every group with infinite centre, a class disjoint from the acylindrically hyperbolic one.
  fpbs-fibre-bubble-forces-mean-field-susceptibility: that proves the mean-field susceptibility bound over a hyperbolic quotient from a uniform fibre bubble by counting fibres instead of supporting sets; this proves that some such detour is forced, because the supporting-set hypothesis itself fails on central fibres.
  fpbs-hyperbolic-quotient-every-generating-set: that is the open target p_c < p_u on groups with an infinite normal subgroup and hyperbolic quotient; this is an obstruction to one proof method on the central part of that class and proves nothing about the thresholds.
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
  - experiments/fpbs-conjugation-expansion-2026-09-17/check_conjugation_expansion.py
  - experiments/fpbs-conjugation-expansion-2026-09-17/output.txt
---

**ESTABLISHED.** Proof route:
`fpbs-cs-set-family-hypothesis-fails-infinite-centre-proof`.

**The hypothesis under test.** Choi–Seo, arXiv:2508.08932v2,
`thm:hutchcroft1plus2` (TeX label line 561, statement lines 562–566, quoted in
`research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md` as CS4):

> Let `\Gamma = Cay(G, S)` be the Cayley graph of a finitely generated group
> `G`. Let `\mathscr{H} = \{H(g) : g \in G\}` be a collection of subsets of
> `G`. Suppose that there exists `R>0` such that the following holds: For
> each finite set `A \subseteq G` there exists `A' \subseteq A` with
> `\#A' \ge \#A / 2` such that for each `a \in A'`, there exists
> `g, h \in G` such that `\|g\|_{S}, \|h\|_{S} \le R`, `A \subseteq a H(g)`
> and `H(g) \cap h H(g) = \emptyset`. Then Equation (Gamma1) holds for
> `\Gamma`.

Call the displayed condition, for a given family `𝓗` and radius `R`,
**SF(𝓗,R)**. It is the only route in [CS] to the susceptibility estimate
(Gamma1) `limsup_(p -> p_c-) (p_c - p) chi_p < infinity`. For acylindrically
hyperbolic groups [CS] verify it through WPD loxodromics (`prop:supportingWPD`,
line 1224; `lem:pigeon`; line 1537).

**Theorem.** Let `G` be finitely generated and `S` a finite generating set.
Write `B(R)` for the closed `R`-ball about `e` in the word metric of `S`, and for
finite nonempty `E ⊆ G` put

```text
D_R(E) = { a h a^-1 : a in E, h in B(R) }.
```

(a) **Necessary condition.** If SF(𝓗,R) holds for some family `𝓗`, then every
finite `A` has at least `#A/2` points `a` for which some `h in B(R)` satisfies
`a h a^-1 ∉ A A^-1`.

(b) **Conjugation-expansion test.** If some finite nonempty `E` satisfies
`#(D_R(E) \ E) < #E`, then SF(𝓗,R) fails for **every** family `𝓗`. The witness
is `A = E ∪ D_R(E)`.

(c) **Infinite centre.** If the centre `Z(G)` is infinite, then for every finite
generating set `S`, every `R > 0` and every family `𝓗`, SF(𝓗,R) fails. The
witness is `A = F ∪ B(R)` for any set `F` of more than `#B(R)` central
elements. So `thm:hutchcroft1plus2` never applies to a Cayley graph of such a
group.

**Class covered by (c).** Every finitely generated group with infinite centre.
This includes:
* `F_2 x Z` on every generating set, Choi–Seo Question 1.3;
* `Lambda x Z^k` for every `Lambda` and `k >= 1`;
* central extensions `1 -> Z -> G -> Q -> 1` with `Q` hyperbolic, including
  the fundamental groups of closed Seifert-fibred 3-manifolds whose regular
  fibre is central (Question 1.6 of [CS] in that case);
* braid groups `B_n` for `n >= 3`, and irreducible spherical-type Artin groups;
* right-angled Artin groups with a central generator.

All of these lie in the target classes of
`fpbs-hyperbolic-quotient-every-generating-set` (when `Q` is non-elementary
hyperbolic) or `fpbs-product-every-generating-set` (when `G` splits as a
product), and none is acylindrically hyperbolic.

**What this changes.** The recorded Attempts on the hyperbolic-quotient class
said that the WPD *remedy* needs acylindricity, which left open whether some
other family of supporting sets could be built from the hyperbolic quotient.
Part (c) closes that: no family works, whatever it is built from. Choi–Seo §2.3
had shown this only for Hutchcroft's half-space family on `F_2 x Z`. The
failing invariant is **conjugation expansion**: SF(𝓗,R) forces
`#(D_R(E) \ E) >= #E` for every finite `E`, and central elements have
`D_R(E) ⊆ B(R)`, which is bounded. The step that dies is the hypothesis of
`thm:hutchcroft1plus2` itself, before Appendix A of [CS] begins. Any proof of
(Gamma1) on these groups must avoid supporting sets with disjoint short
translates, for example by counting fibres as in
`fpbs-fibre-bubble-forces-mean-field-susceptibility`.

**Scope and limits.**
* This obstructs a method, not a conclusion. For `F_2 x Z` with product
  generators the Cayley graph is `T_4 x Z`, which has `p_c < p_(2->2)` by
  `fpbs-hyperbolic-nonunimodular-critical-l2-gap`. By the standard triangle
  condition argument (Remark A.1 of the artifact), (Gamma1) then holds there
  too. So SF is strictly stronger than (Gamma1). This remark is not part of
  the established statement.
* (b) is not invariant under commensurability. It does not decide
  `F_2 x D_infinity`, where the reflection has finite centralizer.
* It does not decide products with a centreless amenable factor either. The
  script finds that the lamplighter `Z/2 wr Z` compresses at `R = 1` but not
  at `R = 2`.
* It says nothing about semidirect products such as `Z^2 ⋊ F_2`, where
  conjugation by the base appears to expand.
* It says nothing about (Gamma2) (`cor:hutchcroftIotaAcyl`), which [CS] prove
  by a separate argument.
