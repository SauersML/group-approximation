---
rg: 2
id: leavitt-single-cycle-trace-controls-finite-sets
kind: claim
title: Finite native identities quantitatively promote the Leavitt cycle trace to every finite set
distinct_from:
  binary-leavitt-full-character-simplex: That classifies exact characters; this gives finite algebraic certificates and explicit bounds for approximate unitary evaluations.
  binary-leavitt-hyperlinear-iff-24k-feasible: That characterizes feasibility and recovers separation by amplification; this proves the feasible tuples themselves have canonical traces.
artifacts:
  - research/artifacts/leavitt-single-c-trace-certificate-2026-09-08.md
---

**Established by a written proof and independent audit; not newly
Lean-verified.** For any finite nonidentity subset of
`H=L_(F_2)(1,2)^x`, chosen native words, and integers `N,M>=2`, `r>=1`,
one can construct finitely many true native relations such that defect
at most `epsilon` on these relations implies

```text
|tr G| <= sqrt(1/N + sqrt(1/M + 3^(-r) + |tr C| + 18 epsilon))
```

for every prescribed word `G`. The argument uses a finite generalized
dihedral group, explicit Leavitt module conjugacies, and two finite
Gram estimates. It requires no finite-simple-group character bounds.

With `tr C=0`, the choices `N>=2 eta^(-2)`, `M>=12 eta^(-4)`,
`3^(-r)<=eta^4/12`, `epsilon<=eta^4/216` give `|tr G|<=eta`.
Thus full-kernel feasible frozen tuples already become canonical
microstates. No feasibility assertion or fixed finite defining packet
follows. Word compilation is effective, with no practical length or
runtime bound claimed.
