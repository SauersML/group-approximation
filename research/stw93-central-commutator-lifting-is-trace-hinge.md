---
rg: 2
id: stw93-central-commutator-lifting-is-trace-hinge
kind: claim
title: Ambient averaging kills the XCIII kernel and central commutator lifting is the exact trace hinge
distinct_from:
  stw93-residual-tracefree-iff-unique-trace: that theorem identifies residual bounded traces with extra traces on D; this theorem gives the intrinsic norm-commutator criterion for excluding those traces and proves that it already holds in the full ultrapower.
  stw93-free-factor-central-sequences-are-tracially-scalar: that theorem is a tracial 2-norm statement for free-factor sequences; this result gives norm self-commutator generation in the full C*-ultrapower and isolates failure of centrality of the commutator factors.
  stw93-saturated-slice-data-allow-residual-trace: that abstract countermodel shows the slice data are insufficient; the present theorem uses the additional realization of D as a relative commutant inside the unique-trace uniform-Dixmier ultrapower A_omega.
  stw93-trace-kernel-quasitracial-invisibility: that open claim concerns all quasitraces; the equivalence here concerns uniqueness of ordinary traces and does not linearize quasitraces.
artifacts:
  - research/artifacts/stw93-central-commutator-lifting-audit-2026-08-30.md
  - research/artifacts/stw93-central-factorization-no-go-audit-2026-08-30.md
---

Put

```text
A=C*_r(F_2) tensor Z,       D=A_omega intersect A',
I=J_tau intersect D.
```

For a C*-algebra `C`, write

```text
Com_sa(C)=closure(span_R{x*x-xx*:x in C}) subset C_sa.
```

Then, unconditionally,

```text
I_sa subset Com_sa(A_omega).                              (ACC1)
```

Thus every XCIII trace-kernel element is already invisible to every bounded
trace on the full norm ultrapower.  The remaining ordinary-trace question is
exactly relative commutator lifting:

```text
D has a unique normalized trace
  iff I_sa subset Com_sa(D).                              (ACC2)
```

Equivalently, `(ACC2)` says that for every self-adjoint `h=[(h_n)] in I`
and every `epsilon>0`, there are a fixed integer `m` and bounded norm-central
sequences `(x_(j,n))`, `1<=j<=m`, such that

```text
lim_omega ||h_n-sum_j(x_(j,n)*x_(j,n)-x_(j,n)x_(j,n)*)||
  < epsilon.                                             (ACC3)
```

Uniform Powers--Dixmier averaging supplies `(ACC3)` with bounded factors in
`A_omega`, but the coordinatewise averaging unitaries need not form central
sequences.  Promoting those ambient factors to elements of `D` is therefore
the exact missing norm-level step; tracial spectral gap alone does not do it.

This promotion cannot follow from a general finite-factorization lemma.
`stw93-abstract-central-factorization-can-fail` gives a uniquely traced
uniform-Dixmier matrix norm ultraproduct and a relative commutant with a
II_1-factor tracial quotient for which an ambient trace-zero projection is
an ambient self-commutator limit but is detected by a trace on the relative
commutant.  Orthogonal central block cutdowns preserve the maximum norm
defect and do not average it.  The actual XCIII argument must therefore use
the faithfully traced full free-factor diagonal, which that countermodel
lacks.
