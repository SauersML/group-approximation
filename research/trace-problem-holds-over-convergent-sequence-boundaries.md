---
rg: 2
id: trace-problem-holds-over-convergent-sequence-boundaries
kind: claim
title: The trace problem holds for W*-bundles over countable bases with finitely many limit points, without property Gamma
distinct_from:
  stw99-problem-xxii-tracial-completion-traces-continuous: that is the general trace problem; this is the established case of a Bauer boundary that is a countable compact space of Cantor--Bendixson derived set finite, where the m-copies argument closes.
artifacts:
  - research/artifacts/stw99-xxii-trace-problem-2026-08-30.md
---

Let `K` be a countable compact metric space whose set of limit points is
finite (e.g. a convergent sequence `ω + 1`, or finitely many of them), and
let `(M, X)` be a W\*-bundle over `K` whose fibres are finite factors (II₁
or matrix algebras) — for instance the algebra of `‖·‖`-bounded,
fibrewise-2-norm-continuous sections `y ↦ a(y) ∈ R_y`.  Then every tracial
state on `M` is `‖·‖_{2,X}`-continuous: `T(M) = X = Prob(K)`-integrals of
the fibre traces.

No property Γ, McDuffness, or separability of the fibres is used; the
fibres being von Neumann factors supplies the spectral projections that
CCEGSTW's CPoU machinery replaces in their ultrapower theorem
(arXiv:2310.20594, Theorem 7.5).  The two results overlap but neither
contains the other: theirs treats ultrafilter quotients whose fibres are
not von Neumann algebras but requires property Γ; this treats honest
convergent-sequence bundles with arbitrary finite-factor fibres.
