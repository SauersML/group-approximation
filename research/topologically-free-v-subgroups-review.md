---
rg: 2
id: topologically-free-v-subgroups-review
kind: claim
title: Referee review of 06a8bda454 (topologically free f.g. subgroups of V are virtually free) — HSZ Theorem A is quoted verbatim (2605.20564v2, p. 1), and items 1, 2 and 3(a)–(c) are correct; item 1 is the general form of HSZ's own Corollary 1.7 argument (the case Z²), which should be credited; Lemma L and the compression step are correctly marked open
distinct_from:
  topologically-free-fg-subgroups-of-v-are-virtually-free: that is the lane claim under review; this checks it at the HSZ source and adds the credit to HSZ Corollary 1.7.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof 06a8bda454 by bh-scout-bbmz).** Read at
source: Hyde–Skipper–Zaremsky, *Action graphs, semiconjugacy, and non-embedding in Thompson's group V*,
arXiv:2605.20564v2 (29 May 2026), pp. 1–7.

## Verdicts

| item | verdict |
|---|---|
| HSZ Theorem A quotation | **PASS**, verbatim (p. 1) |
| (F1) `Fix(v) = U_v ⊔ P_v`, `int Fix(v) = U_v` | **PASS** |
| (F2) germ group at a fixed point embeds in `Z` | **PASS** |
| 1. free orbit ⇒ virtually free | **PASS**; credit HSZ Cor. 1.7 |
| 2. topologically free ⇒ virtually free | **PASS** |
| 3(a)–(c) structure of non-virtually-free `G` | **PASS** |
| Lemma L, compression step | **correctly marked OPEN** (claim, route, and the Q4.7 node) |
| "first constraint using a property of `V` that `R` lacks" | not checked; a remark, not a claim |

## Checks

- **Theorem A (p. 1), verbatim.** "Let G be a finitely generated subgroup of V, with S a finite symmetric generating
  set for G. Let X be the G-orbit of some κ₀ ∈ ℭ, and let Γ be the action graph for G acting on X, that is, the
  Schreier graph with respect to the subgroup Stab_G(κ₀). Then Γ is quasi-isometric to a tree."
  - HSZ use right actions, and the node's left notation is harmless.
  - HSZ's "group of germs at x" (p. 3) is the one used in (F2).
- **(F1).** The three cases on a cone `w_iℭ → u_iℭ` are exhaustive:
  - `u_i = w_i`: the whole cone is fixed.
  - `|u_i| = |w_i|` but `u_i ≠ w_i`: nothing in the cone is fixed.
  - One prefix properly extends the other: the only possible fixed point is `s^∞`.
  - Neither prefix is a prefix of the other: nothing is fixed.

  So `P_v` has at most one point per cone. A point of `P_v` is not interior, because its cone is open and holds only
  one fixed point.
- **(F2).** `germ ↦ |u| − |w|` is invariant under extending both prefixes by one letter, which gives common
  refinements. It is additive once the representatives are aligned so that `u_1 = w_2`, and it is injective
  because `|u| = |w|` forces `u = w`. So the germ group is a subgroup of `Z`, nontrivial only at eventually periodic
  points.
- **Item 1.** With a trivial stabilizer the orbit is a free `G`-set, so the action graph is `Cay(G, S)`. Theorem A
  makes it a quasi-tree, and a finitely generated group quasi-isometric to a tree is virtually free (standard).
  - **This is exactly HSZ's proof of their Corollary 1.7** ("every subgroup of V isomorphic to ℤ² intersects
    Stab_V(κ₀) non-trivially"), stated in general. The node should cite Cor. 1.7 as the prototype.
- **Item 2.** If every `g ≠ 1` has empty interior of `Fix(g)`, then by (F1) each `Fix(g)` is finite. `G` is
  countable, so the union is countable, while `ℭ` is uncountable. So a free orbit exists.
- **Item 3.**
  - *(a) `K` is countable.* `O` and `K` are invariant, since `h·int Fix(g) = int Fix(hgh⁻¹)`. A point of `K` off
    the countable set `E = ⋃ P_g` would have trivial stabilizer, so `K ⊆ E`.
  - *(b) Stabilizers are infinite cyclic.* The germ map on `Stab_G(x)` is injective for `x ∈ K`. Its image is a
    nontrivial subgroup of `Z`, nontrivial by item 1, hence infinite cyclic, and `x` is eventually periodic.
  - *(c)* This is Theorem A at `κ₀ = x`.
- **Open items.** Both are open everywhere they appear:
  - The claim's "What remains … (open)" lists them.
  - The route marks "Lemma L (open; sketch only)" and says of the compression step "Nothing on main supplies this
    yet".
  - The Q4.7 node's update says "Open: Lemma L … and a compression step".
  - The claim's status line covers only items 1–3.

## Lesson for general BH

- **What Theorem A gives.** It turns "`V` has quasi-tree orbit graphs" into a dichotomy for finitely generated
  subgroups: virtually free, or almost everywhere locally trivial with cyclic point stabilizers on a countable
  closed set.
- **The next step toward Q4.7.** Any one-ended subgroup lives on the second side. So the next step is exactly the
  node's Lemma L: quotients of one-ended hyperbolic groups by cyclic subgroups are not quasi-trees.
