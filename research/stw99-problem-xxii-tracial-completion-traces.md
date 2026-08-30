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
  - research/artifacts/stw22-asymptotically-dense-factor-field-audit-2026-08-30.md
  - research/artifacts/stw22-variable-factor-selection-audit-2026-08-30.md
  - research/artifacts/stw22-uncountable-cofinite-bundle-audit-2026-08-30.md
  - research/artifacts/stw22-intrinsic-zero-dimensional-selection-audit-2026-08-30.md
  - research/artifacts/stw22-stabilized-l2-selection-audit-2026-08-30.md
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
The matrix-stage hypothesis can now also be removed.
`stw22-dense-factor-fields-have-uniform-traces`
allows arbitrary nuclear unique-trace subalgebras `D_n` of the ambient UHF
algebra, without nesting or finite dimensionality, provided only that
`dist(u,D_n)->0` for every ambient element.  The GNS fibres at finite
coordinates may already be proper hyperfinite `II_1` subfactors.  Norm
density makes their trace-preserving expectations converge to the identity
in `2`-norm, so the same derived-subset descent proves trace continuity over
every closed finite-height pattern.
The finite-height restriction disappears under a common-ambient
expectation hypothesis.
`stw22-expectation-fields-have-uniform-traces` treats any compact
metrizable zero-dimensional base when all factor fibres sit in one finite
factor and their trace-preserving expectations vary pointwise continuously
in `2`-norm.  A moving-factor perturbation lemma makes the weighted-copy
multifunction lower semicontinuous; clopen selection then produces
orthogonal copies inside the moving fibres themselves.  This kills the
escaping quotient at every countable limit rank and covers arbitrary
countable successor and limit Cantor--Bendixson height without transfinite
descent.  The unresolved boundary is whether general factorial tracial
bundles possess such a continuous common-ambient expectation presentation.

There is also a nonmetrizable positive class requiring no common ambient
factor.  `stw22-finite-derived-set-factor-bundles-have-uniform-traces`
removes countability and metrizability from the convergent-sequence theorem:
every factorial tracial bundle over a compact Hausdorff base with finitely
many nonisolated points has only uniform traces.  Around one such point the
base is the one-point compactification of an arbitrary discrete space.  A
small spectral cut then has countable support automatically, because only
finitely many coordinates can have trace above `1/n`; its fibrewise
orthogonal copies are therefore uniform `2`-limits of finite central sums.
This supplies exactly the assembly step missing from naive disintegration.

The finite-derived-set and common-ambient restrictions can now both be
removed in covering dimension zero.
`stw22-zero-dimensional-factor-bundles-have-uniform-traces` proves the
trace conclusion for every factorial tracially complete C*-algebra over an
arbitrary compact zero-dimensional Hausdorff base.  An exact tuple in one
factor fibre is lifted to bundle sections; a uniform weighted polar
correction produces nearby exact tuples without selecting the jumping
support projections; finite disjoint clopen refinements then converge to
global orthogonal weighted copies.  Thus the result needs neither
metrizability nor a common ambient factor and covers every compact
scattered boundary as well as perfect zero-dimensional boundaries.

For countably generated factorial bundles, that frontier now begins in
dimension two.  `stw22-dim1-factor-bundles-have-uniform-traces` stabilizes
the intrinsic Hilbert `C(K)`-module of `L^2` sections into the standard
module `C(K,ell^2)`.  The varying-factor weighted-copy sets thereby become
a lower-semicontinuous, uniformly locally path-connected family of closed
subsets of one complete metric space.  One-dimensional selection produces
exact global copies, and a fibrewise spectral-clipping lemma shows that the
selected `L^2` contractions actually belong to the original tracially
complete C-star algebra.  Countable generation is automatic for uniform
completions of separable C-star algebras; no common ambient factor or local
triviality is used.

For arbitrary factorial bundles in dimension at least two, the remaining
input is now separated cleanly from the topological colouring step.
`stw22-intrinsic-local-replication-colouring-reduction` shows that no common
ambient factor, fixed comparison corners, or local trivializations are needed
after exact local replication tuples exist.  Over a `d`-dimensional compact
metrizable base, a `(d+1)`-coloured refinement gives a range bound `d+1`
independent of the replication number and kills every gap trace.  The
quantitative weighted correction lemma proves lower semicontinuity of the
fibrewise solution relation.  Stabilized selection uses only path
connectedness and uniform local path connectedness in dimension one.  In
higher dimensions it would require corresponding uniform local
`k`-connectedness through `k=d-1`; establishing or refuting those stronger
connectivity estimates is the precise finite-dimensional frontier.

Bare projectivity of finite-dimensional matrix cones does not bypass this
frontier. `stw22-bare-cone-projectivity-does-not-supply-ilr` gives a trivial
matrix field over the interval and a positive section satisfying the strict
ILR trace bound with a global replication tuple. A fibre map from
`C_0((0,1]) tensor M_(m+1)` has an explicit unrestricted global lift, but no
local lift can keep its `e_00` corner equal to the prescribed section: that
would force the source support and all `m` range supports to be mutually
orthogonal, costing one support copy more than ILR. Thus a relative
prescribed-corner cone theorem would be genuinely stronger input, not a
formal consequence of cone projectivity.

The rank-efficient reformulation uses `M_m`, counts `a^(1/2)` itself as the
first range copy, and is exactly an anchored form of ILR. It avoids the extra
support copy but not the essential issue: the lifted `e_00` corner must equal
the prescribed section on a neighborhood, whereas projectivity controls it
only in the original fibre.

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
