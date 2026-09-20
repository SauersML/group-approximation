---
rg: 2
id: one-ended-hyperbolic-v-locally-fixed-review
kind: claim
title: Referee review of 22ee40f8ae (Lemma L and local fixing for one-ended hyperbolic subgroups of V) — adversarial check of the bottleneck argument finds it correct; items 1 and 2 follow; the compression lemma is correctly left open
distinct_from:
  one-ended-hyperbolic-subgroups-of-v-are-locally-fixed: that is the lane claim under review; this checks Lemma L step by step, and items 1–2.
  topologically-free-v-subgroups-review: that review passed the input 3(a)–(c); this reviews the step that empties the exceptional set K.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; adversarial review of the lane proof 22ee40f8ae by
bh-scout-bbmz).** Lemma L is plausibly folklore (relative ends of cyclic subgroups), and no priority is claimed.

## Verdicts

| item | verdict |
|---|---|
| Schreier graph = `⟨c⟩\Cay(Γ,S)`, with metric `min_n d(x, c^n y)` | **PASS** (right cosets match HSZ's right action) |
| bottleneck necessity for quasi-trees | **PASS** (easy direction of Manning) |
| choice of `U`, `ξ ∉ ⟨c⟩η`, arc `J` | **PASS** |
| (E1) heights `≥ R − C_1` on rays over `J` | **PASS** |
| (E2) high path `P` | **PASS** |
| (E3) every quotient geodesic has a low midpoint | **PASS** (the use of `ξ ∉ Hη` is essential and correct) |
| item 1 (`K = ∅`, finite clopen cover) | **PASS** |
| item 2 (disjoint supports; no north–south element), torsion-free case | **PASS** |
| compression lemma | correctly **open** |

## The adversarial points checked

1. **Which Schreier graph.** HSZ's action graph uses right cosets and right multiplication. That is the quotient
   of `Cay(Γ, S)`, with edges `g — gs`, by the left `⟨c⟩`-action. It is a free action by graph automorphisms, so
   paths lift and `d̄([x],[y]) = min_n d(x, c^n y)`.
2. **Lifting quotient geodesics.** A quotient geodesic of length `D` lifts to a path of length `D` from `x_ξ` to
   some `c^n x_η`. Since `D` is the minimum over lifts, that lift is an `X`-geodesic.
3. **(E1) compactness.** An unbounded Gromov product `(ζ_k | c^(n_k) o)` would force `ζ_k → c^±`, which is
   impossible because `J` is compact and misses `c^±`. The estimate `(x | y)_o ≤ (ζ | y)_o + O(δ)` for `x` on
   `[o, ζ)` is standard, since `(x|y)_o ≤ d(o, x)`.
4. **(E2) fellow travelling.** Choose `t_i` along `J` with `(t_i | t_(i+1)) ≥ R`, possible by uniform continuity
   for a visual metric. Their radius-`R` points are then `O(δ)` apart, and the height is 1-Lipschitz for `d̄`.
5. **(E3), the crux.** The triangle `(o, c^n o, c^n η)` is thin.
   - `c^n x_η` cannot be near `[o, c^n o]`: that segment is near `⟨c⟩o` by quasiconvexity, while
     `ht([x_η]) ≥ R − C_1`.
   - So it is near `[o, c^n η)`, and `(x_ξ | c^n x_η)_o ≤ (ξ | c^n η)_o + O(δ)`.
   - Then `sup_n (ξ | c^n η)_o < ∞` needs two facts: `c^n η → c^±` because `η ≠ c^∓`, and `ξ ≠ c^n η` for every
     finite `n`. The second is exactly why `ξ ∉ Hη` was chosen.
   - Hence the lifted geodesic passes within `C_3 + 4δ` of `o`.
   - Both endpoints have height between `R − C_1` and `R`. So the near point `q` is within `C_5` of the midpoint,
     and the midpoint has bounded height.
6. **Bottleneck.** In a space quasi-isometric to a tree, every path between the endpoints passes within `Δ` of
   the midpoint of every geodesic between them: push forward, and note that removing a ball separates a tree.
   The high path `P` stays at height `≥ R − C_1 − C_2`, but a `Δ`-neighbourhood of the midpoint has height
   `≤ C_6 + Δ`. That is a contradiction for large `R`.
7. **Sanity checks.**
   - For virtually free `Γ`, `∂Γ` is a Cantor set and no `U` exists, consistent with quasi-tree quotients.
   - For a surface group, `⟨c⟩\H²` is a hyperbolic annulus with circle-boundary funnels. That is not a
     quasi-tree, matching the lemma.

## Items 1 and 2

- **Item 1.**
  - The input: 3(b) of the refereed partial gives cyclic stabilizers `⟨c_x⟩`, and 3(c) makes `Γ/⟨c_x⟩` a
    quasi-tree. Lemma L forbids that, so `K = ∅`.
  - Compactness and refinement then give disjoint clopen pieces, each fixed pointwise by a nontrivial element,
    since subsets of fixed sets are fixed.
- **Item 2, disjoint supports.**
  - Disjoint open supports force commuting, and in a torsion-free hyperbolic group commuting elements lie in a
    common cyclic subgroup.
  - The standard power argument (`supp(h^j) ⊆ supp h`) then gives `z^(ij) = 1`, a contradiction.
- **Item 2, north–south elements.**
  - With `w^n(C ∖ B) ⊆ A`, the conjugate `w^(−n) g_a w^n` fixes `C ∖ B` pointwise, so its support lies in `B`.
    Meanwhile `supp g_r ⊆ C ∖ B`.
  - These are disjoint nontrivial supports, which the first bullet excludes.
- **The compression lemma.** Correctly marked open, and correctly shown to suffice via item 2.

## Lesson for general BH

- **Boundary connectivity, as a statement about the Schreier graph.** One-endedness becomes coarse
  non-tree-likeness of every cyclic Schreier graph, witnessed by an arc of `∂Γ ∖ {c^±}`.
- **How it combines with HSZ.** HSZ's quasi-tree theorem then forces one-ended subgroups of `V` to be "locally
  trivial everywhere".
- **Where Q4.7 now sits.** Entirely in the dynamics of single elements of `V`: several attractors, and periodic
  regions.
