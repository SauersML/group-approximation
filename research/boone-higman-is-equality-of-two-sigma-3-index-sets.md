---
rg: 2
id: boone-higman-is-equality-of-two-sigma-3-index-sets
kind: claim
title: Boone-Higman says two Sigma_3 index sets coincide; the decidable one is Sigma_3-complete, so under Boone-Higman the embeddable one is too
distinct_from:
  common-decidable-hosts-iff-uniform-word-problem: that is about common hosts for classes of presentations; this is about the index sets of single presentations, i.e. the arithmetic complexity of recognizing which presentations are decidable and which embed in a finitely presented simple group.
  boone-higman-uniform-in-word-problem-algorithms: that is the uniform version of the conjecture; this is the non-uniform conjecture recast as an equality of index sets.
  index-set-profinitely-closed-is-pi3-complete: that computes the index-set complexity of a different group property; this computes it for decidability and for embeddability in finitely presented simple groups.
---

**ESTABLISHED** (lane proof, not reviewed; route
`boone-higman-is-equality-of-two-sigma-3-index-sets-proof`). No priority is claimed.
That decidability of the word problem is Σ_3-complete is probably folklore. The
family `G_U` and the splitting lemma below are this lane's own.

**Index sets.** Fix the generators `a, t`. For an index `i` of a c.e. set of words,
let `G_i = ⟨a, t | W_i⟩`. Define:
- `DEC = {i : G_i has solvable word problem}`;
- `EMB = {i : G_i embeds in a finitely presented simple group}`.

Define `DEC_fp` and `EMB_fp` the same way for finite presentations.

1. **Upper bounds.** All four sets are `Σ_3`, and `EMB ⊆ DEC`, `EMB_fp ⊆ DEC_fp`
   (Kuznetsov, `simple-envelope-forces-solvable-word-problem`).
2. **The conjecture as an equality.** `boone-higman-conjecture` holds iff
   `EMB = DEC`, iff `EMB_fp = DEC_fp`. The finitely presented version follows by
   `clapham-fp-embedding-preserves-word-problem`.
3. **Completeness.** `DEC` is `Σ_3`-complete. Explicitly, `COF ≤_m DEC` through the
   circulant graph wreath products
   `G_U = ⟨a, t | [a, t^k a t^-k] = 1 (k ∈ U)⟩ = A(Γ_U) ⋊ Z`, whose word problem is
   uniformly Turing-equivalent to `U`. The reduction combines this with the
   splitting lemma of the proof route: there is a uniform c.e. `U_i` that is
   cofinite when `W_i` is cofinite, and noncomputable when `W_i` is coinfinite.
   `DEC_fp` is also `Σ_3`-complete, granted the standard uniform degree-preserving
   Higman–Clapham embedding. That uniformity is cited, not re-read.
4. **Under Boone–Higman,** `EMB` and `EMB_fp` are `Σ_3`-complete.
5. **Unconditional hardness of `EMB` reduces to one test family.** Suppose every
   `G_U` with `U ⊆ N_{≥1}` cofinite embeds in a finitely presented simple group.
   This is `circulant-graph-wreath-products-satisfy-boone-higman`, now ESTABLISHED (lane proof). So the
   same reduction gives `COF ≤_m EMB`, and `EMB` is `Σ_3`-complete with no
   hypothesis: `embedding-in-fp-simple-groups-is-sigma-3-complete`.

**Reading.**
- A disproof of Boone–Higman must exhibit a gap between two `Σ_3`-complete-type
  sets, since `DEC` is `Σ_3`-complete. In particular it cannot come from any
  property of presentations that is `Π_3` or simpler.
- A proof must reach at least the "cofinite corner" of the circulant family. The
  easiest members are already not subgroups of `V`; see the test-family node.
