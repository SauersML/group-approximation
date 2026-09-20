---
rg: 2
id: level-set-route-reaches-only-bounded-rover-nekrashevych-groups
kind: claim
title: For a finitely generated contracting self-similar group G, every element of V_{d,r}(G) has zero defect, and V_{d,r}(G) is a bounded RSG exactly when the non-identity nucleus graph has no path between distinct cycles and no strongly connected component other than a single cycle; so the bounded-RSG F_infinity theorems (defect-free, torsion-defect, level-set) reach exactly the bounded-automata case, already proved by Belk-Hyde-Matucci, and the open part of the Skipper-Zaremsky question is the exponential-activity case
requires:
  - bounded-defect-free-full-contracting-rsgs-are-f-infinity
distinct_from:
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the Skipper-Zaremsky question itself; this shows which part of it the bounded-RSG machinery can reach, and that the part it reaches is already known.
  level-set-join-complexes-are-highly-connected: that proves F_infinity for bounded RSGs with Z-valued interval defect; this shows Roever-Nekrashevych groups never have nonzero defect, so that theorem's new content never applies to them.
  contracting-groups-have-dying-kernel-covers-of-type-fn: that is the cover route to the same question; this locates the case that route still has to supply.
---

**ESTABLISHED (lane proof, bh-sz-vdg, 2026-09-19; elementary; Referee bh-ref-e 2026-09-19, PASS with repairs,
`rover-nekrashevych-activity-and-level-set-scope-review`; repairs applied: first-return loops in case (E), BHM credit
in row (P), Sidki credit).** It is a scoping
result about a method. It does not settle the Skipper-Zaremsky question.

**Setting.** `G ≤ Aut(T_d)` is finitely generated, self-similar and contracting, with nucleus `N` (finite, closed
under sections, containing `1`). `Γ = V_{d,r}(G)`. By BBMZ, Γ is a full contracting RSG over the full `d`-shift
(recalled, not re-read). Singular points and defect are as in `bounded-defect-free-full-contracting-rsgs-are-f-infinity`:
`p ∈ sing(g)` if `g` agrees with no element of `V_{d,r}` on any cone around `p`.

**The nucleus graph.** `𝒩` has vertex set `N ∖ {1}`, with an edge `n → n|_x` for each letter `x` such that
`n|_x ≠ 1`.

## Theorem

1. **Zero defect.** `d_g(p) = 0` for every `g ∈ Γ` and every `p ∈ sing(g)`.
2. **Singular rays.** For `g ∈ G`, `sing(g)` is the set of rays `ξ` with `g|_{ξ_{≤n}} ≠ 1` for all `n`. For
   `g ∈ Γ`, `sing(g)` is a finite union of images of such sets under prefix replacements.
3. **Trichotomy.** Exactly one of the following holds, and it is decided by the finite graph `𝒩`:
   - **(B)** every strongly connected component (SCC) of `𝒩` is a single cycle or trivial, and no path joins two
     distinct cycles. Then every `sing(g)` is finite, i.e. Γ is **bounded**.
   - **(P)** every SCC is a single cycle or trivial, but some path joins two distinct cycles. Then every `sing(g)`
     is countable, and some is infinite.
   - **(E)** some SCC is not a single cycle. Then some `sing(g)` has the cardinality of the continuum.
4. **Consequence.** The bounded-RSG theorems on main apply to Γ exactly in case (B). Case (B) is the class of
   bounded automata groups, for which `V_{d,r}(G)` is `F_∞` by Belk–Hyde–Matucci (arXiv:2407.03149, abstract,
   read at source: "if G is a bounded automata group then the associated Röver-Nekrashevych groups V_{d,r}G have
   type F_∞"). So the level-set lemma gives nothing new for Skipper–Zaremsky, since its `ℤ`-defect content
   needs nonzero defect, which item 1 rules out.

## Proof

1. **Zero defect.** This is Proposition 2, item 4 ("surjective nucleus") of
   `bounded-defect-free-full-contracting-rsgs-are-f-infinity`. For a small cone `C_α` around `p`, `g` acts on it as
   the nucleus element `g|_α` followed by a prefix replacement, and `g|_α` maps the whole subtree onto itself. So
   `g(C_α)` is a single cone of the same type, and `[g(C_α)] = [C_α]`. Every section of a Röver–Nekrashevych
   element is a tree automorphism, which is the surjective-nucleus hypothesis.
2. **Singular rays.** On the cone `C_v`, `g ∈ G` acts by `vw ↦ g(v)·g|_v(w)`. It agrees with a prefix replacement
   `vw ↦ uw` on `C_v` iff `u = g(v)` and `g|_v` acts trivially, and `G` acts faithfully, so iff `g|_v = 1`. Since
   `g|_{vx} = (g|_v)|_x`, once a section along `ξ` is trivial all later ones are. This proves the first sentence.
   An element of Γ is, on each cone of a finite partition, a prefix replacement followed by an element of `G`.
   That gives the second.
3. **Trichotomy.** By contraction, for every `g ∈ G` there is a level `m` at which all sections of `g` lie in `N`.
   So `ξ ∈ sing(g)` iff the path `(g|_{ξ_{≤n}})_{n≥m}` is an infinite path in `𝒩`. Conversely, every infinite
   path in `𝒩` starting at `n ∈ N` is a singular ray of `n ∈ G`. Up to the finitely many prefixes of length `m`,
   singular sets are therefore sets of infinite paths in the finite graph `𝒩`. Such a path eventually stays in one
   SCC, and on the way it passes through finitely many SCCs.
   - In case (B), a path from a vertex can make only finitely many choices before settling into a cycle, which it
     then follows forever. So there are finitely many infinite paths from each vertex.
   - In case (P), for a path from cycle `C_1` to cycle `C_2`, the paths that loop `k` times around `C_1` and then
     settle in `C_2` are distinct for distinct `k`. So there are infinitely many. The set is countable, because each
     path is determined by finitely many exit times between single cycles.
   - In case (E), an SCC that is not a single cycle has a vertex `v` with two distinct out-edges inside the SCC.
     Each extends to a *first-return* loop at `v`, a closed walk that meets `v` only at its ends, and the two loops
     differ in their first edge. First-return loops form a prefix code, so distinct infinite concatenations of them
     are distinct infinite paths. Paths from a fixed vertex are determined by their labels, so this gives `2^ℵ₀`
     singular rays (repair of bh-ref-e: arbitrary loops need not concatenate injectively).
4. **Consequence.** Item 1 gives zero defect, so `bounded-defect-free-full-contracting-rsgs-are-f-infinity`
   (Theorem 1, itself an attribution to BHM Remark 2.13) applies whenever Γ is bounded, i.e. in case (B).
   - Case (B) is exactly BHM's class of bounded automata groups. Their definition is that each `g` has only
     finitely many infinite words with all sections nontrivial, i.e. finite `sing(g)` by item 2. The proof is in
     `rover-nekrashevych-polynomial-activity-tower-review`.
   - The torsion-defect and level-set theorems also assume boundedness, so they reach no further. ∎

## What this leaves for Skipper–Zaremsky

| Case | Status for `V_{d,r}(G)` |
|---|---|
| (B) bounded | `F_∞`: Belk–Hyde–Matucci. Röver's group is also re-proved on main by `wreath-recursion-thompson-groups-inherit-fn` |
| (P) polynomial | `F_∞`: **BHM Remark 2.14** (their sketch). The complete proof is item 1 of `rover-nekrashevych-polynomial-activity-tower-sigma-full`, refereed PASS twice (`rover-nekrashevych-polynomial-activity-tower-review`, `rover-nekrashevych-activity-and-level-set-scope-review`) via BHM's main finiteness theorem along the activity tower. Its Σ items are unreviewed |
| (E) exponential | **open** in general. `F_∞` via dying-kernel covers holds for IMGs of every PCF rational map (`pcf-rational-nekrashevych-groups-are-f-infinity`, via orbifold covers; unreviewed) and of expanding coverings of compact aspherical spaces (`hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity`) |

- (B) ∪ (P) is exactly polynomial activity growth in that node's sense, one degree for all elements. This is
  Sidki's circuit theorem (S. Sidki, *Automorphisms of one-rooted trees: growth, circuit structure, and acyclicity*,
  J. Math. Sci. 100, 2000; recalled) applied to the nucleus automaton. A self-contained proof is in
  `rover-nekrashevych-polynomial-activity-tower-review`. So after that review, V_{d,r}(G) is `F_∞` for every
  contracting G in cases (B) and (P), and the Skipper–Zaremsky question is open exactly in case (E).
- **Lesson.** For Röver–Nekrashevych groups the singular-set trichotomy is the activity trichotomy. Defect is
  always zero, so the question is purely about the cardinality of singular sets. The BBMZ-host phenomenon of
  nonzero defect at branch points does not arise.
- **Next case in (E), now done.** Sub-hyperbolic PCF rational maps are handled by
  `pcf-rational-nekrashevych-groups-are-f-infinity`, with the orbifold group as a dying-kernel cover (lane proof,
  unreviewed). The torsion obstruction in `contracting-groups-have-dying-kernel-covers-of-type-fn` is consistent with
  it, since the orbifold group's torsion is exactly the recurrent branching.
- **Remaining in (E).** Contracting groups not of dynamical origin.
