---
rg: 2
id: hls-ghost-class-never-lifts-to-the-bernoulli-full-shift
kind: claim
title: Over every host with isometrically embedded large-girth expanders, a full-shift Bernoulli class vanishing on the tree boundary has eventually zero ranks on the marked expanders
distinct_from:
  hls-ghost-lift-needs-forest-shift-failure: that shows, under (H-K), that a class with ghost ranks would refute the forest-shift comparison; this shows that no such class exists, with no (H-K) or forest-shift hypothesis.
  forest-shift-bernoulli-comparison-is-surjective: that asks surjectivity of the cylinder comparison at the forest shift; this restricts to the CND-support shift instead, where the comparison is an isomorphism, and leaves the forest question open.
  hls-ghost-projection-breaks-k-exactness: that is HLS's non-exactness for the marking subshift and its ghost projection; this shows that the ghost class is not the image of any full-shift class.
---

**ESTABLISHED** by `hls-ghost-class-never-lifts-via-cnd-restriction` (unreviewed). Full proof:
`research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`, Section 6 (Theorem D).

**Setting.**
- `G` is a finitely generated torsion-free group satisfying hypotheses (M) of `hls-ghost-lift-needs-forest-shift-failure`:
  isometrically embedded `D`-regular expanders `A_n ⊆ G`, `D >= 3`, with girth tending to infinity, strictly increasing
  sizes and `d(A_n, A_m) -> ∞`.
- `Λ` is any finite alphabet with `0 ∈ Λ` and `|Λ| >= 2`, `X = Λ^G` and `X^0 = X \ {0}`. The marked configurations are
  `x_n = 1_(A_n)` for a fixed symbol `1 ≠ 0`, `Ŷ = closure(∪_n G·x_n)` and `∂Y = Ŷ \ ∪_n G·x_n`.
- `r_x = K_0(π_x)` is the rank at a finite-support configuration (`bernoulli-assembly-injective-beyond-the-host`,
  item 1).

**Theorem.** Let `y ∈ K_0(C_0(X^0) ⋊_r G)` with `y|_(∂Y) = 0` in `K_0(C_0(∂Y \ {0}) ⋊_r G)`. Then `r_(x_n)(y) = 0` for
all but finitely many `n`.

**Consequences.**
- `hls-ghost-class-lifts-to-the-bernoulli-full-shift` is false: no prime `p` and host satisfying (M), with or without
  (H-K), carry a class with `y|_(∂Y) = 0` and `r_(x_n)(y) ≠ 0` for infinitely many `n`.
- The HLS projection `p` has `r_(x_n)[p] = 1` for every `n` and `q_∂[p] = 0` (`hls-ghost-projection-breaks-k-exactness`,
  context). So `[p]` is not the image of any class along `C_0(X^0) ⋊_r G -> C_0(Ŷ \ {0}) ⋊_r G`.
- The theorem of `hls-ghost-lift-needs-forest-shift-failure` has an unsatisfiable hypothesis, so it is vacuous. It stays
  true.
- **Corollary E** (artifact, Corollary 6.2). For every finitely generated torsion-free `G`, the classes
  `[1_(C_s ∩ T_cnd)]` over patterns with CND support, one per orbit, form a `Z`-basis of `K_0(C_0(T_cnd \ {0}) ⋊_r G)`,
  and `K_1 = 0`.
- **What a Bernoulli witness must look like.** Let `y ∉ im T_r` over a torsion-free host. Then `y - T_r(n(y))` restricts
  to `0` on `T_cnd`. So it is invisible to every finite-pattern rank and to every closed invariant set of CND-support
  configurations, tree-like boundaries included.

**Why it holds.**
- Restrict `y` to `T_cnd`. There the cylinder comparison is an isomorphism, so the restriction is a cylinder combination
  `m'`. Ranks and Möbius inversion identify `m'` with the pattern expansion `n(y)` on CND patterns.
- The tree boundary lies in `T_cnd`, so `b_(m') = y|_(∂Y) = 0`.
- Reduced assembly at `∂Y` is injective, and topological K-theory is half-exact. So the combination on `Ŷ` comes from
  `K_0(C_0(∪_n G·x_n) ⋊_r G) = ⊕_n Z`, and its counts on `A_n` vanish for large `n`.
- Locality: coefficients of `n(y)` vanish on patterns of large diameter. Small patterns inside `A_n` are trees, hence CND,
  so the counts of `m'` on `A_n` equal the ranks of `y` at `x_n`.

**Model tests.**
- A one-site cylinder `[1_(C_s)]` has ranks `|A_n|` but does not vanish on `∂Y`, consistent.
- For `G = Z` or free groups with a free basis, `T_cnd = X` and (M) fails. The theorem is empty there, as it should be.

**Scope.**
- Torsion-free finitely generated hosts. (H-K) is not assumed; it holds anyway (`expander-tree-boundary-k0-max-reduced-injective-proof`).
- Rests on `bernoulli-pattern-expansions-are-finite` (unreviewed) for locality.
- (F) (`forest-shift-bernoulli-comparison-is-surjective`) is not decided.
