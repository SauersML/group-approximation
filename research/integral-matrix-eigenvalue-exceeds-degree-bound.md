---
rg: 2
id: integral-matrix-eigenvalue-exceeds-degree-bound
kind: claim
title: Some group has an integral self-adjoint matrix with an eigenvalue whose von Neumann multiplicity exceeds n over its degree
distinct_from:
  determinant-conjecture-counterexample-exists: that asks for any determinant violation; this asks for one sharper shape, a heavy or transcendental eigenvalue, which forces a violation but is not forced by one
  kun-thom-wreath-galois-unequal-atomic-element: that asked for a purely atomic spectrum with unequal conjugate masses and is refuted; this allows any continuous part and asks for a single atom heavier than one over its degree
  galois-invariance-implies-algebraic-eigenvalues: that proves transcendental eigenvalues are impossible under Aut(C/Qbar)-invariance of kernel dimensions; this asks for a group where such an eigenvalue, or an over-heavy algebraic one, occurs
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

**OPEN.** Exhibit a group `G`, a self-adjoint `A in M_n(Z[G])` and
`lambda in R` with

```text
dim_(N(G)) ker(r_A - lambda) > n / deg(lambda),
```

for instance a transcendental eigenvalue. By
`heavy-eigenvalue-gives-determinant-counterexample` this refutes Lück's
determinant conjecture through an explicit box-principle polynomial `Q(A)`
(route `determinant-counterexample-from-heavy-eigenvalue`). It would also
refute the algebraic eigenvalue conjecture of Dodziuk--Linnell--Mathai--Schick--Yates,
which Thom proves for sofic groups (arXiv:math/0701294v3, Theorem 1.1).

**Necessary shape.**
- **`G` nonsofic.** Sofic groups satisfy the determinant conjecture, hence the
  degree bound.
- **Infinite spectrum.** Finite spectrum gives rational, Galois-equal masses
  over every group (`finite-spectrum-integral-elements-obey-determinant`), and
  equal masses on `deg(lambda)` conjugates obey the bound.
- **Spectrum of capacity at least one.** Smaller capacity forces finite
  spectrum over every group (`integral-spectra-of-small-capacity-are-finite`).
- **No Aut(C/Qbar)-invariance** of kernel dimensions if `lambda` is
  transcendental (`galois-invariance-implies-algebraic-eigenvalues`).

## Attempts

- **Finitely many atoms, Galois-unequal.** Dead for every group, by the
  finite-spectrum bullet above (`kun-thom-wreath-galois-unequal-atomic-element`
  is refuted the same way).
- **Heavy rational eigenvalue.** Impossible: `deg = 1` and the multiplicity of
  any eigenvalue is at most `n`. The first testable shapes are an eigenvalue
  of degree `d >= 2` with multiplicity above `n/d`, and a transcendental
  eigenvalue.
- **Where to look, untried.** An isolated algebraic eigenvalue of a mixed
  element over a nonsofic support: a Kun--Thom wreath (lamps mixed with actor
  letters) or the nine-leaf Leavitt group. Its projection lies in `C*_r(G)`
  and not in the group algebra, so neither Zalesskii nor soficity controls
  its trace. A heavy eigenvalue would be a stronger monster than a bare
  determinant violation: the degree bound is the whole atom content of the
  conjecture (`serre-class-atoms-obey-degree-bound`).
