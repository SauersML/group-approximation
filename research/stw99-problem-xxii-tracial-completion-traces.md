---
rg: 2
id: stw99-problem-xxii-tracial-completion-traces
kind: claim
title: Every trace on a uniform tracial completion is uniformly 2-norm continuous (STW Problem XXII)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw22-tracial-completion-fibre-gap-audit-2026-08-30.md
  - research/artifacts/stw22-low-spectrum-boundary-extension-audit-2026-08-30.md
  - research/artifacts/stw22-all-degree-weighted-selection-audit-2026-08-30.md
  - research/artifacts/stw22-locally-trivial-bundle-audit-2026-08-30.md
  - research/artifacts/stw22-matrix-to-hyperfinite-field-audit-2026-08-30.md
  - research/artifacts/stw22-finite-bratteli-cube-audit-2026-08-30.md
---

**Problem XXII of Schafhauser--Tikuisis--White, *Nuclear C*-algebras:
99 problems*, arXiv:2506.10902v2.**  Let `A` be a C*-algebra with nonempty
compact trace space `T(A)`, and let

```text
M=completion of A in ||a||_(2,T(A))=sup_(tau in T(A)) tau(a*a)^(1/2).
```

Must every tracial state on `M` be continuous for the uniform `2`-norm?
Equivalently, does restriction identify

```text
T(A)=T(M)?
```

The problem remains open in general, including for nuclear `A`.  The source
records positive answers for finite-dimensional trace simplices, for
completions with complemented partitions of unity, and in further Bauer
cases.

For trivial UHF fields the new spectral-band theorem crosses every finite
selection threshold.  `stw22-finite-dimensional-trivial-field-traces`
proves the desired trace equality for the uniform completion of
`C(X) tensor U` whenever `X` is compact metrizable and has finite covering
dimension.  Conjugator fibres have uniform sphere-filling moduli in every
finite degree by controlled Michael selection and the Popa--Takesaki
contraction.  A weighted boundary frame is then split into countably many
bands on which its polar frame is continuous; recursive orthogonal fillings
have an exact uniform `L^2` tail.  This supplies all finite equi-`LC^n`
inputs without assuming continuous support projections.  The earlier
dimension-two theorem is retained as the first new special case.

For locally trivial hyperfinite W*-bundles over finite-dimensional compact
metrizable bases, `stw22-locally-trivial-finite-dimensional-bundles` gives
an independent cocycle-local recovery of the same conclusion.  This is not
a larger bundle class: Evington--Pennig, arXiv:1601.05964, prove that every
locally trivial W*-bundle with all fibres `R` is globally trivial, without
a dimension restriction.  The retained local proof chooses orthogonal
corners independently in product charts; a `(d+1)`-coloured refinement
makes only one chart active per colour, so it reproduces the gap estimate
without first constructing the global trivialization.

For a tracially continuous `C(X)`-bundle with factor `2`-norm fibres, the
exact elementary obstruction is now isolated by
`stw22-norm-fibre-gap-is-the-trace-obstruction`.  A trace supported at
`x in X` factors automatically through the C*-norm fibre, but need not
factor through the smaller `2`-norm fibre.  Thus fibrewise uniqueness of the
II_1 trace does not by itself solve the problem.

The gap need not vanish.  The intrinsic sufficient condition established in
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` is that every
`K_x/J_x` carry no nonzero bounded positive trace.  Stability of all the gap
ideals is a concrete special case, strictly weaker than `J_x=K_x`.

The equality shortcut already fails in an actual zero-dimensional nuclear
Bauer completion.  The computation
`stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap` exhibits a
nonzero `K_x/J_x` and proves directly that it is bounded-trace-free by
orthogonal replication of spectral cuts.  It also isolates the remaining
general difficulty as neighbourhood-wise continuous selection rather than
pointwise finite-factor comparison.
`stw22-rank-one-scattered-fibre-gaps-are-tracefree` extends this computation
to every locally Cantor--Bendixson-rank-one point and proves the trace
conclusion for the trivial UHF field over compact scattered bases of height
at most two.  On higher-rank scattered bases, it localizes any remaining
obstruction to the second derived set.
`stw22-height-three-scattered-trace-continuity` then
resolves the next Cantor--Bendixson layer for compact metrizable bases.  Its
two-level argument quotients onto the rank-one skeleton and uses spectral
square roots to damp discontinuous fibrewise orthogonalizers in the kernel.
The successor mechanism is now isolated in
`stw22-derived-set-gap-trace-reduction`: restriction to the derived set is
surjective on fibre gaps and has bounded-trace-free kernel.  Finite
iteration proves the trace conclusion for every compact metrizable
scattered base of finite Cantor--Bendixson height; limit rank remains open.

There is also an unconditional changing-fibre class beyond trivial and
locally trivial `R`-bundles.  In
`stw22-matrix-to-hyperfinite-field-trace-continuity`, an increasing dense
matrix chain `F_n` in a UHF algebra gives a nuclear continuous field over a
convergent sequence with fibre `F_n` at `n` and hyperfinite `II_1` fibre at
the limit.  Its only gap is nonzero but bounded-trace-free by finite-matrix
orthogonal replication.  Hence every trace on its uniform completion is
uniform, despite the changing fibre type and infinite Bauer boundary.
This one-dimensional construction is now closed under arbitrary finite
tensor products and restriction to any closed subfield by
`stw22-finite-bratteli-cubes-have-only-uniform-traces`.  The resulting
closed subsets of `(N union {infinity})^d` have Cantor--Bendixson height at
most `d+1` and include rooted Bratteli patterns; the full cube has full
matrix fibres on its open stratum and infinitely many hyperfinite fibres on
intersecting boundary faces.  A nearest-point conditional-expectation lift
across each derived subset makes restriction surjective; square-root
damping kills every trace on its kernel.  Finite descent therefore
eliminates all fibre-gap traces, although the full cube's top gap is
nonzero.

## Attempts

For a Bauer-style central bundle, disintegrate an extreme trace over the
center.  This only proves that the trace factors through the norm fibre
`M/J_x`.  The canonical finite-factor fibre is instead `M/K_x`, with
`J_x` contained in `K_x`.  Fibrewise uniqueness therefore applies only
after one proves that every trace on `M/J_x` kills `K_x/J_x`.  The linked
norm-fibre-gap theorem makes this obstruction exact.  Equality `J_x=K_x`
holds for norm-continuous trivial fields, but uniform `2`-norm completeness
alone does not supply it, so the direct disintegration argument stops
precisely at this ideal gap.
