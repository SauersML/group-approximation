---
rg: 2
id: stw93-faithful-full-diagonal-retains-norm-kernel
kind: claim
title: A faithful full-factor diagonal can retain a nonzero norm trace kernel
distinct_from:
  stw93-abstract-central-factorization-can-fail: that countermodel produces an extra relative-commutant trace by putting a trace-zero projection in the defining algebra, so its diagonal trace is not faithful; this construction has a faithful diagonal with the actual free-factor spectral gap, but its trace-zero projection has infinite multiplicity escape and is killed by every relative-commutant trace.
  stw93-free-factor-central-sequences-are-tracially-scalar: that theorem identifies the image of actual free-factor central sequences in the tracial quotient; this construction proves that faithful full-factor diagonal data alone do not remove nonzero norm-central classes before taking that quotient.
  stw93-central-commutator-lifting-is-trace-hinge: that theorem asks whether every element of the actual XCIII kernel is a central self-commutator limit; this result supplies a broad class of faithful-diagonal kernel projections for which central trace invisibility follows from multiplicity, while isolating failure of multiplicity escape as the remaining possible obstruction.
artifacts:
  - research/artifacts/stw93-faithful-diagonal-multiplicity-escape-audit-2026-08-30.md
---

Let `A` be a unital monotracial MF algebra with faithful trace `tau`.  There
is a faithful trace-preserving embedding

```text
Phi:A -> M=product_omega M_(N_k)
```

such that, for `D=M intersect Phi(A)'` and the trace-kernel ideal `J_tau` of
`M`,

```text
J_tau intersect D
```

contains a nonzero projection `p`.  Thus faithfulness of the diagonal and
full-factor spectral gap do not upgrade tracial centralization to norm
centralization and do not make the norm trace kernel vanish.

The construction does not change the tracial GNS representation of `A`.
Consequently it retains every fixed adjoint `L^2` spectral-gap inequality in
that representation, including the free-factor-relative inequality used for
`L(F_2) tensor_bar R` in XCIII.

The projection is nevertheless invisible to every bounded trace on `D`.
For every fixed `n`, it has `n` pairwise orthogonal Murray--von Neumann
equivalent copies in `D`.  Hence every normalized trace `q` on `D` satisfies
`n q(p)<=1` for all `n`, and therefore `q(p)=0`.  In particular

```text
p in Com_sa(D).
```

This applies to `A=C*_r(F_2) tensor Z`: its trace is faithful, the
free-factor part of its GNS algebra has the fullness spectral gap used in
XCIII, and `A` is MF.  Consequently those two diagonal inputs alone still
permit norm-one trace-kernel projections.  What prevents the construction
from being a negative XCIII model is exactly its **multiplicity escape**.
Any trace-charged positive kernel element in the actual central sequence
algebra must fail to admit arbitrarily many orthogonal Cuntz-equivalent
copies in the relative commutant.
