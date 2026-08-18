---
rg: 2
id: twisted-tower-central-character-criterion
kind: claim
title: The central-character separation criterion decides the coordinate regime of compressor rigidity
distinct_from:
  char-p-root-torsion-collapse: that reduces every finite-dimensional representation of G to a finite congruence-type quotient extended by a central relative-K1 piece; this identifies EXACTLY when that central piece can hurt, and turns the modulo clause into a finite decision problem.
  approximate-collapse-for-kt-compressor: that is the approximate-representation wall; this is the last question of the GENUINE-representation regime, and — unlike everything else in the lane so far — it has a live refutation side.
artifacts:
  - research/char-p-root-torsion-collapse.md
---

**Question (OPEN, finite, two-sided).**  For the finite central
extensions `Ē = E/E_r(J)` arising from finite-codimension ideals
`J ⊆ R` via `char-p-root-torsion-collapse` (central kernel
`K(R,J)` = relative `K₁`, over the finite quotient `EL_r(R/J)`):

```text
(CC)  Can two irreducible unitary representations of Ē with DISTINCT
      central characters on K(R,J) have ISOMORPHIC restrictions to
      the image of the compressed copy Λ?
```

**Why (CC) is decisive for the coordinate regime.**  In any
finite-dimensional representation, the failure locus of the (CCR)
consequence is exactly `[x, z]` for `z` in the central piece
(`char-p-root-torsion-collapse-proof` §4).  In an irreducible
representation `z` acts as a scalar and commutes with everything —
no witness.  A witness needs a reducible representation where `z`
acts by different scalars on two blocks AND some `x ∈ ρ(Λ)'` mixes
the blocks — i.e. a nonzero `Λ`-intertwiner between two irreps with
different central characters: precisely (CC).  Hence:

- **(CC) = NO** (the `Λ`-restriction determines the central
  character): the central piece can never hurt, the modulo clause of
  `char-p-root-torsion-collapse` evaporates, and (CCR) holds for
  EVERY coordinatewise ultraproduct of genuine finite-dimensional
  representations of `G` — the coordinate regime closes completely,
  with no `SK₁` vanishing needed.
- **(CC) = YES, trace-faithfully assemblable** (a tower of such pairs
  with `tr ρ_n(g) → 0` for `g ≠ e`): the intertwiners `x_n` assemble
  into `x ∈ σ(Λ)' ∖ σ(Γ)'` — an EXPLICIT counterexample to (CCR),
  killing `kt-centralizer-normalization-hs` and the rigidity route,
  by K-theory.  This would be the lane's first refutation-side
  object, and notable independently (a K-theoretic obstruction to
  Hilbert–Schmidt normalization).

**The central pieces are genuinely nontrivial — VERIFIED
(2026-08-18 K-theory verification pass; full ledger in the sweep
record).**  The pinning is unconditional: for ANY ideal,
`(SL(R,J) ∩ E(R))/E(R,J) ≅ coker(K₂(R) → K₂(R/J))` (Weibel K-book
III Thm 5.7.1 + Def 2.2; `SK₁(R) = 0` — Suslin 1977 Cor 7.11
directly for Laurent rings, `r ≥ 3` sharp — makes this the standard
relative `SK₁`).  `K₂(R) ≅ (ℤ/(q−1))^d ⊕ ℤ^{d(d−1)/2}` on unit
symbols (Quillen's fundamental theorem for regular rings, Weibel
V.6.3, iterated; for `q = 2`: free abelian on `{x_i, x_j}`).
Two hard facts about the target:

- **DEAD FAMILY:** `K₂(𝔽_q[x]/(x^e)) = 0` for EVERY `e` (van der
  Kallen 1971, char 2 included via perfectness; Hesselholt–Madsen
  1997 in even degrees) — the original dual-numbers testbed was
  provably vacuous and the entire single-variable truncated family
  with it.  Design fence (sweep's inference, elementary): whenever
  `R^× ↠ S^×` and `K₂(S)` is symbol-generated, the cokernel
  vanishes — a testbed must break one of the two.
- **LIVE ARENA (verified ingredients; assembly = sweep's
  construction):** `S = 𝔽_2[C_2×C_2] ≅ 𝔽_2[x,y]/(x²,y²)` has
  `K₂(S) ≅ (ℤ/2)³` (Zhang arXiv:2401.11210 Lem 2.3, read with
  proof).  For `d = 2`: `R ↠ S`, `x₁ ↦ 1+x`, `x₂ ↦ 1+y` is a
  well-defined surjection, `K₂(R) = ℤ·{x₁,x₂}` has image of order
  ≤ 2, so `coker ⊇ (ℤ/2)²` and **`SK₁(R,J) ≠ 0`**.  For the actual
  KT ring (`d = 3`, since `G ↠ SL_d(ℤ)` Kazhdan needs `d ≥ 3`):
  compose with `x₃ ↦ 1` — the symbols `{x_i, x₃}` die on the
  trivial unit (`{u,1} = 1` by bilinearity), the image is again
  `≤ ℤ/2`, and the cokernel survives.  All VERIFIED (third sweep
  pass), with two sharpenings: the image is exactly `ℤ/2`
  (`⟨x,y⟩ = ⟨y,x⟩ ≠ 0` in Zhang's basis — skew-symmetry, not
  vanishing — modulo the sweep's flagged reading of Zhang's
  generator correspondence), so **`coker ≅ (ℤ/2)² exactly, order
  4`**; and the compatibility the collapse step needs HOLDS: the
  COMPRESSED subring also surjects onto `S`, since monomials map
  through exponent parities and `A ∈ SL_d(ℤ)` is invertible mod 2 —
  so `π̄(Λ) = π̄(Γ) = π̄(E)` for this `J`, as
  `char-p-root-torsion-collapse-proof` requires.

So the modulo clause of `char-p-root-torsion-collapse` is NOT
removable: nontrivial central pieces exist for the KT ring itself,
and (CC) is genuinely the decisive question.

**Compute target (finite, size CORRECTED — enumeration is out).**
The true scale: `|S| = 16`, `|m| = 8` (the maximal ideal is
3-dimensional: `x, y, xy`), `ker(GL₃(S) → GL₃(𝔽₂)) = 1 + M₃(m)` has
order `8⁹ = 2²⁷`, `det` is onto `S^×` of order `2³`, so
`|SL₃(S)| = 168·2²⁴ ≈ 2.8 × 10⁹` — 128× the node's earlier
`2^{17}`-scale estimate (caught by the sweep's recomputation) — and
`|Ē| ≈ 1.1 × 10¹⁰` with the central `(ℤ/2)²`.  Brute-force character
tables are NOT feasible; and no cheaper testbed exists (`r ≥ 3`
forced twice — HVZ centrality, Suslin `SK₁ = 0` — and the whole
`𝔽_q[x]/(x^e)` family is dead), so the size is intrinsic.  The
honest approach is STRUCTURAL: decide (CC) by Clifford theory
relative to the order-4 central subgroup — per central character `χ`,
the `χ`-isotypic blocks are projective representations of `EL₃(S)`
with the corresponding cocycle class, and the congruence filtration
`1 + M₃(m) ⊇ 1 + M₃(m²)` (abelian successive quotients) gives a
handle with no enumeration.  (Approach = sweep's proposal, flagged
as proposal.)  A YES does not yet refute (CCR) (trace-faithful
assembly remains); a NO across the natural family is strong evidence
the coordinate regime closes.

**Fences.**  Nothing here touches
`approximate-collapse-for-kt-compressor` (Becker–Lubotzky's
far-from-genuine representations are outside every genuine tower,
twisted or not).  And (CC) = YES does not by itself refute (CCR):
the tower must also be trace-faithful, which constrains how the
paired irreps can recur as quotients grow.
