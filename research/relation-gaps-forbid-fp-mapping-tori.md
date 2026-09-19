---
rg: 2
id: relation-gaps-forbid-fp-mapping-tori
kind: claim
title: A kernel whose relation lengths have unbounded multiplicative gaps has no finitely presented mapping torus, so no torus of a graded small cancellation Tarski monster is finitely presented
distinct_from:
  fp-mapping-torus-iff-finite-automorphic-presentation: that identifies finite presentability of a torus with (FAP1) for some unknown finite data; this gives an intrinsic, checkable metric invariant of the kernel alone that rules out (FAP1) for every automorphism at once.
  tarski-monster-tori-evade-compression-and-stage-lifts: that leaves item 4 of its survivor list (finite presentation of P) untouched; this kills item 4 unconditionally, so no automorphism of the monster can supply (L3).
  torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical: that is the open existence claim (LK1)-(LK3); this proves that its (LK2) fails for every kernel with unbounded relation gaps, including every graded small cancellation kernel.
  hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan: that makes the monster a conditional (L1) candidate; this shows the candidate can never meet (L2)/(LK2), whatever (RF_Γ) says.
artifacts:
  - research/relation-gaps-forbid-fp-mapping-tori-proof.md
  - research/oos-graded-small-cancellation-scales-separate.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/tarski-monster-tori-evade-compression-and-stage-lifts.md
---

**ESTABLISHED.** Proof: `relation-gaps-forbid-fp-mapping-tori-proof`.
Parts A and B are self-contained. Part C uses the verbatim OOS import
`oos-graded-small-cancellation-scales-separate`. Part D uses the established
`kazhdan-torsion-free-tarski-monster-satisfies-kk`.

## Invariant: relation gaps

Let `K = F(X)/N`, with `X` finite. For `R ≥ 0`, let `N_{≤R}` be the normal closure in `F(X)` of
`{w ∈ N : |w| ≤ R}`. This gives an increasing filtration of `N` with union `N`.

- A **gap of ratio `C` at scale `R`** means `N_{≤CR} = N_{≤R} ≠ N`.
- `K` has **unbounded relation gaps (UG)** over `X` if for every `C ≥ 1` and every `R_0` there is a
  gap of ratio `C` at some scale `R ≥ R_0`.
- `K` has **`C`-bounded gaps** over `X` if there is `R_0` such that `N_{≤CR} ≠ N_{≤R}` for all
  `R ≥ R_0`.

If `K` is not finitely presented, then `N_{≤R} ≠ N` for every `R`, and `K` fails UG exactly when
it has `C`-bounded gaps for some `C`.

## Theorem

**A (gap lemma for mapping tori).** Let `ψ ∈ Aut(K)`. Choose words `w_x`, `v_x` representing
`ψ(x)` and `ψ^{-1}(x)`, and put `L = max_x(|w_x|, |v_x|)`. Suppose `P = K ⋊_ψ Z` is finitely
presented. Then there is `R_1` such that for every `R ≥ R_1`:

```text
N_{≤LR} = N_{≤R}   ⟹   N_{≤R} = N.                                  (GAP)
```

Hence either `K` is finitely presented, or `K` has `L`-bounded gaps over `X`. In particular, if `K`
has (UG) over some finite generating set, then no mapping torus `K ⋊_ψ Z` is finitely presented,
for any `ψ ∈ Aut(K)`.

**B (split extensions).** The same conclusion holds for `K ⋊_φ H` with `H` finitely presented and
`φ: H → Aut(K)` arbitrary. `L` is then the Lipschitz constant of the substitutions for the
generators of `H` and their inverses, and `R_1` also depends on the relator lengths of `H`.

**C (graded small cancellation gives UG).** If `K` has a graded small cancellation presentation
`⟨X | ⋃ R_i⟩` (a `Q(.01,10^6)`-presentation in the sense of OOS) and is not finitely presented,
then `K` has (UG) over `X`. More precisely, the stage kernels `N_n` satisfy `N_{≤R} = N_n` on
intervals `[m_n, λ_n)` with `λ_n / m_n → ∞`.

**D (the monster).** Let `Q` be the torsion-free Tarski monster quotient of a torsion-free
non-cyclic hyperbolic group, from `kazhdan-torsion-free-tarski-monster-satisfies-kk`. This includes
the Kazhdan monster over a cocompact `Sp(n,1)` lattice. Then:
- `Q` is not finitely presented and has (UG);
- **no mapping torus `Q ⋊_ψ Z` is finitely presented**, for any `ψ`;
- more generally, no split extension `Q ⋊ H` with `H` finitely presented is finitely presented.

This is unconditional: there is no `(RF_Γ)` and no assumption on the outer order of `ψ`.

**E (consequence for the flagship).** Let `(G, K)` witness `torsion-free-sofic-exact-mf-radical-over-z`.
Then `K` is finitely generated, because it has (T), and `G = K ⋊_ψ Z`. By A, either `K` is finitely
presented (region (AT) of `finite-outer-order-radical-witnesses-cross-alekseev-thom`), or `K` has
`L_ψ`-bounded relation gaps over **every** finite generating set. In the second case, by C, `K` has no graded
small cancellation presentation over any finite generating set.

## What dies

**Class killed:** every flagship / (LK1)-(LK3) witness whose kernel has unbounded relation gaps.

- **Named invariant:** the relation-gap ratio `sup{C : N_{≤CR} = N_{≤R} ≠ N at arbitrarily large R}`.
- **Death step:** finite presentation of the torus, that is (L3) / (LK2) / (FAP1). At a gap scale
  of ratio `L_ψ`, the truncated kernel `N_{≤R}` is `ψ^{±1}`-invariant, so `F/N_{≤R} ⋊ Z` is a
  finitely presented cover of the torus that retracts onto it. This forces `N_{≤R} = N`.

Members:

| member | why it has (UG) |
|---|---|
| OOS torsion-free Tarski monsters over any torsion-free hyperbolic group, including Kazhdan ones | C + D |
| every infinitely presented graded small cancellation group, over its presenting generators | C |

The whole w14 monster-kernel branch of `tarski-monster-tori-evade-compression-and-stage-lifts`
therefore dies at its survivor item 4, whatever happens to items 1-3 and to `(RF_Γ)`.

## What survives

An (IO) witness kernel must be infinitely presented with bounded gaps. Every scale window `[R, L R]`
must contain a genuinely new relation, so the number of distinct scales among
`{N_{≤R}}_{R ≤ T}` grows at least like `log_L T`, which is proved.

Heuristically, not proved: this is the signature of finite `L`-presentations and of
self-similar (branch-type) groups, where a substitution of stretch `L` creates new relators at
every scale `L^k`.

Proved: every graded small cancellation construction is excluded as a source of (IO) kernels,
however the MF and soficity requirements are met. Any other sparse-limit construction dies the
moment its gaps are shown to be unbounded over one generating set.
