---
rg: 2
id: canonical-trace-does-not-control-moving-root-orthogonality
kind: claim
title: Canonical fixed moments do not control moving-coefficient root orthogonality
distinct_from:
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that preserves an arbitrary tensor-stable edge obstruction while forcing the full fixed-word character to be canonical; this gives an explicit two-root moving-frequency model for the failed tensor-isometry inference.
  opposite-root-orthogonality-charges-two-jump-gauges: that proves exact moving-coefficient orthogonality in a left regular finite quotient because the two root subgroups intersect trivially; this shows fixed-moment convergence alone does not pass that identity to ultraproduct root algebras.
  regular-iwahori-relative-congruence-exactification: that may force the needed arithmetic structure using edge compatibility; this rules out obtaining it from the regular character by itself.
---

Canonical trace convergence on every fixed word does not imply a uniform
tensor-isometry for polynomials whose degrees move with the matrix
dimension.

For primes `N->infinity`, let `omega_N=exp(2 pi i/N)` and let

```text
U_N=diag(1,omega_N,...,omega_N^(N-1)).
```

Choose integers `q_N->infinity` with `q_N=o(N)` and put
`L_N=U_N^(q_N)`.  For every fixed pair `(a,b) in Z^2\{(0,0)}`,

```text
tr(U_N^a L_N^b)=tr(U_N^(a+q_N b))=0                  (CMR1)
```

for all sufficiently large `N`: the exponent is nonzero modulo `N` and a
nontrivial clock power has trace zero.  Thus the limiting character on
every fixed word of `Z^2` is canonical.

Nevertheless `W^*(U_N)=W^*(L_N)` (because `q_N` is invertible modulo the
prime `N`).  The multiplication map

```text
L^2(W^*(U_N)) tensor L^2(W^*(L_N)) -> L^2(M_N)
```

cannot be an isometry: its domain has dimension `N^2`, its image lies in
the same `N`-dimensional diagonal algebra, and the moving relation

```text
L_N=U_N^(q_N)                                         (CMR2)
```

exhibits the collision explicitly.

In a canonical group ultraproduct, the fixed subgroup algebras
`W^*(u)` and `W^*(l)` do have the expected orthogonality when the abstract
root subgroups intersect trivially.  But a sequence of correcting gauges
with conductor-dependent Fourier support belongs to the larger Loeb
ultraproduct of the coordinate root algebras, not necessarily to those
separable fixed subgroup algebras.  `(CMR1)--(CMR2)` proves that scalar
canonical moments cannot bridge this inclusion.

Therefore globalizing
`opposite-root-orthogonality-charges-two-jump-gauges` requires a genuinely
uniform moving-coefficient theorem derived from edge compatibility and the
full cubic/Weyl relations.  Such a theorem would be substantive relative
congruence capture, not a consequence of central-regular localization.

