---
rg: 2
id: free-group-avatar-router
kind: route
title: Present the routed quotient over a rank-two free group with long avatar words
target: bespoke-routing-lemma
requires: [greendlinger-free-product-lemma]
artifacts:
  - GroupApproximation/Sofic/SmallCancellationRouter.lean
---

## The architecture

By [[free-product-router-factor-embedding-obstruction]], no
factor-embedding regime can produce the routing datum, so the quotient
is NOT built over `E ∗ B` with syllable small cancellation.  Instead:

Fix presentations `E = ⟨g₁..g_p | r⟩`, `B = ⟨h₁..h_q | r'⟩`, a free
pair `a, b` inside the defect `N ≤ E` (available hypothesis-free from
the suitable-defect module), and the protected `s ∈ N`.  Present

    Q := F(y₁, y₂) / ⟨⟨R⟩⟩

and DEFINE the factor maps on generators by long aperiodic avatar
words: `φ : E → Q`, `g_i ↦ W_i(y)`; `ψ : B → Q`, `h_k ↦ U_k(y)`.  The
relator family `R` consists of

1. every relator of `E`'s presentation rewritten through the `W`'s, and
   every relator of `B`'s rewritten through the `U`'s — this and only
   this is what makes `φ` and `ψ` well-defined homomorphisms, and each
   such relator is LONG because the avatars are long;
2. tying relators `y_j · (word in the avatars of designated N-elements)⁻¹`
   — these put `y_j ∈ φ(N)`, so `Subgroup.map φ N = ⊤` and `φ` is onto;
3. tying relators `y_j · (word in the U_k)⁻¹` — these put
   `y_j ∈ ψ(B)`, so `ψ` is onto and (T) descends.

Two-generation is by presentation.  Finite presentation is finitely
many relators over a finite-rank free group.  Survival of the protected
element is the already-checked engine (`injOn_mk'_of_greendlinger`)
applied to the avatar word of `s`, whose length is designed below twice
the minimal relator length.  Torsion-freeness is the free-group C'(1/6)
torsion theorem (no relator a proper power), the companion half of
[[greendlinger-free-product-lemma]].  Everything therefore consumes
ONLY the free-group forms: the Greendlinger gate and its torsion
companion.  The relative CoprodI forms are no longer on the critical
path of [[torsion-free-non-mf-from-bespoke-router]].

## Remaining constructive work

The avatar words must be produced explicitly with: pairwise-aperiodic
long blocks giving whole-family metric `C'(1/6)` after symmetrization;
no proper powers; the rewritten relators of clause 1 kept cyclically
reduced (pad with block-separators); and the protected-ball length
margin.  This is finite word combinatorics with no group theory in it —
the classical Rips-style disjoint-exponent-interval pattern — and is
the W3 workstream of notes/TORSION_FREE_NON_MF_LEAN_PLAN_2026-08-21.md;
the coordinator supplies the explicit family and its piece ledger.

One honest caution: clause 1 rewrites `E`'s relators, among them the
Britton/HNN relations of the skeleton, through the avatars; the
rewritten words must be checked aperiodic AGAINST the tying relators as
well — the piece ledger is a joint condition on the whole family, not
per-clause.
