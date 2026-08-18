---
rg: 2
id: approximate-collapse-for-kt-compressor
kind: claim
title: The congruence collapse of the compressor survives approximate representations
distinct_from:
  kt-centralizer-normalization-hs: that is the full normalization/(CCR) question; this is its one remaining wall after the 2026-08-18 campaign — the step-3 identification — promoted to a first-class claim so routes can require it.
  el-r-polynomial-robust-spectral-gap: that (closed by citation) supplies uniform spectral gap for almost representations — the OTHER former gap; this is the collapse statement that no spectral-gap property supplies.
  compressor-coset-two-point-exact: that proves the collapse for genuine congruence quotients (E-normality, π(Γ) = E); this asks whether any trace-faithful APPROXIMATE representation can break it.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**Question (OPEN) — the (AC) wall, in commutation-tolerant form.**
Let `σ = "∏_𝒰 π_n" : G → U(M)` be trace-faithful into a tracial matrix
ultraproduct, `Λ = tΓt⁻¹` the compressed Kazhdan copy, and
`x = (x_n) ∈ σ(Λ)' ∩ M` with `‖x‖ ≤ 1`.  Must

```text
lim_𝒰  dist₂( π_n(γ) ,  { u ∈ U(d_n) : ‖[x_n, u]‖₂ ≤ ε_n } ∩ π_n(Λ)·𝔅_n ) = 0
```

for every `γ ∈ Γ` — i.e. does the congruence-level image collapse
`π(Γ) ⊆ π(Λ)` (true in EVERY genuine finite quotient, by E-normality)
survive the passage to approximate representations, at least against
the commutant of a given `x`?  A positive answer (for every such `σ`)
combined with the citation-closed uniform spectral gap
(`el-r-polynomial-robust-spectral-gap`) completes
`kt-centralizer-normalization-hs` via
`hs-normalization-via-robust-spectral-gap` — and with it the rigidity
route to the first non-hyperlinear group.

**What is known (2026-08-18 campaign, all in the parent node and its
sibling claims):**

- TRUE for every coordinatewise ultraproduct of genuine
  representations, UNCONDITIONALLY — the collapse hypothesis is
  automatic: `ρ(Λ) = ρ(E)` identically across all of FD
  (`fd-invisibility-of-compression`), so the coordinate regime is
  fully closed and any counterexample here must violate an IDENTITY
  of finite-dimensional representation theory, not a generic
  property (`ccr-for-coordinate-collapsing-models` supplies the
  (T)-uniformity step).
- The group-algebra slice cannot break it (`ccr-group-algebra-slice`:
  `FC_Λ(G) = Z`), nor can coarse-bimodule content, amplification,
  finite quotients, small-block gluing, or the bicommutant shortcut
  (impossible: `σ(γ) ⊥ L²(σ(Λ)'')`).
- Becker–Lubotzky FORCES the question to be about far-from-genuine
  approximate representations (Γ is not HS-stable; the liftable case
  is vacuous), and Ioana's is the only engine making controlled
  far-from-genuine ones — blocked when a factor has (T).
- The ambient published frontier is Alekseev–Thom OP 6.2 (2026-08-05);
  its part (b) with conjugation-coherent lifts would convert this
  question to finite-dimensional form.  Peterson 2605.16669 does not
  answer it (Gate 1 final, all sections now read from PDF): his §6 is
  Popa intertwining adapted to ultraproducts of FREE PRODUCTS —
  amenable-amalgam hypotheses throughout, conclusion shape "locate
  the algebra", never "compare two commutants" — with no analogue for
  matrix ultraproducts.  Two useful residues from his paper: the
  printed (T)-interchange precedent and templates (see the route
  node), and the SHAPE of his Prop 6.2 — rigidity-implies-confinement
  (a rigid subalgebra's relative commutant cannot escape a
  distinguished part of the ambient); no such theorem exists for
  matrix ultraproducts, but a matrix-ambient analogue would constrain
  where any counterexample to this claim could live.

**Stakes, stated once:** a proof refutes hyperlinearity of the
Kun–Thom wreath group (first non-hyperlinear group; group-CEP
refuted; Pestov 3.9 falls).  A refutation kills the rigidity route
while leaving both answers to Q3.4 possible.  Either way one of
Pestov's two remaining questions is directly advanced.
