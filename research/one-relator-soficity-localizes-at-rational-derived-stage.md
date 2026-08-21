---
rg: 2
id: one-relator-soficity-localizes-at-rational-derived-stage
kind: claim
title: Soficity of a one-relator group is equivalent to soficity of a finite rational-derived term, which is free-by-rationally-perfect
distinct_from:
  residually-rationally-solvable-one-relator-sofic: that is the positive corollary in the case where the finite term is free, and it closes a whole class outright; this is the underlying equivalence, which decides nothing on its own and holds for every one-relator group including the unresolved ones.
  linton-radical-abelianization-is-truncated-group-ring: that computes the first homology of the radical as a module; this locates *where in the group* the soficity question lives and says nothing about homology.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

ESTABLISHED.  Let `G = F/<<w>>` be a one-relator group and let

    G_Q^(0) = G ,   G_Q^(i+1) = ker( G_Q^(i) --> H_1(G_Q^(i); Q) ) ,
    R = G_Q^(ω) = ∩_{i<ω} G_Q^(i)

be its rational derived series and rationally perfect radical.  Then there is
an `n <= |w|` such that, writing `E = G_Q^(n)`:

1. `G/E` is solvable, hence amenable;
2. `E/R` is free — so either `E` is free (`R = 1`) or `E ≅ R ⋊_α F₀` for a free
   group `F₀` and some `α : F₀ → Aut(R)`;
3. **`G` is sofic if and only if `E` is sofic.**

Part 3 is the point.  It is an *equivalence*, not a sufficient condition: the
whole of Pestov's Question 4.9 sits inside the shell `E`, and `E` is a very
particular object — free-by-(normally-one-generated rationally perfect) — not
an arbitrary group.

## Proof

**(1)** The rational derived series is characteristic, so `E ⊴ G`, and
`G/E ⊵ G_Q^(1)/E ⊵ ⋯ ⊵ 1` is a finite normal series whose factors are
quotients of `G_Q^(i)/G_Q^(i+1)`, torsion-free abelian by construction.  So
`G/E` is solvable and therefore amenable.

**(2)** By Linton's Theorem 1.1 (arXiv:2407.09272) there are `r ∈ F` with
`|r| <= |w|` and `k >= 1` with `w ∈ r^k[<<r>>_F, <<r>>_F]` and
`R = G_Q^(ω) = <<r>>_G`.  Since `w ∈ <<r>>_F`, the quotient `G/R = F/<<r>>` is
again a **one-relator group**, with relator `r`; and Linton's corollary says it
is residually rationally solvable.  His Corollary 1.2(2) then gives an
`n <= |r| <= |w|` with `(G/R)_Q^(n)` free.

It remains to identify `(G/R)_Q^(n)` with `G_Q^(n)/R`.  That is the following
lemma, applied with `A = G`.

> **Lemma.**  If `R ⊆ A_Q^(ω)` then `(A/R)_Q^(i) = A_Q^(i)/R` for all `i < ω`.
>
> *Proof.*  Induct on `i`, the case `i = 0` being trivial.  Put `B = A_Q^(i)`,
> so `(A/R)_Q^(i) = B/R` by induction, and note `R ⊆ A_Q^(ω) ⊆ A_Q^(i+1) =
> B_Q^(1)`.  Since `B ↠ B/R`, we have `aR ∈ (B/R)_Q^(1)` iff `a^m ∈ [B,B]R` for
> some `m >= 1`.  But `[B,B]R ⊆ B_Q^(1)`, so `a^m ∈ B_Q^(1)`, and `B/B_Q^(1)`
> is torsion-free abelian by construction, whence `a ∈ B_Q^(1) = A_Q^(i+1)`.
> The reverse inclusion is immediate.  ∎

So `G_Q^(n)/R = (G/R)_Q^(n)` is free.  A free quotient splits — lift a free
basis arbitrarily and use the universal property — giving `E ≅ R ⋊ F₀`.

**(3)** Forward: soficity passes to subgroups.  Backward: `1 → E → G → G/E → 1`
has sofic kernel and amenable quotient by (1), so `G` is sofic by Elek--Szabó.
∎

## Why the proof is written out rather than cited

The source audited here attributes the two-case finite-stage statement to
Linton directly.  Only the **free** case is his Corollary 1.2; the R-by-free
case is not a quoted sentence of that paper.  Deriving it as above from the two
sentences that *were* read verbatim from the source (Theorem 1.1 and Corollary
1.2(2), transcribed in the artifact) keeps this node off a transcription
premise, which the standing zero-literature order would otherwise make
unusable.

## What it does and does not buy

It buys the exact shape of any counterexample: not residually rationally
solvable, nontrivial infinitely generated radical, and the nonsoficity already
present in `E`.  It does **not** continue from `E` to `R`: passing from a sofic
`R` to a sofic `R ⋊ F₀` is not a permanence property anyone has, and the
generic form of it is false — see
[[sofic-semidirect-product-closure-fails]].
