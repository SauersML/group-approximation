---
rg: 2
id: titz-witzel-cat0-lattices-citation
kind: route
title: Import Titz Mite-Witzel Theorem A and Corollary B and derive freeness, torsion-freeness and the Brown identification
target: titz-witzel-simple-kazhdan-cat0-lattices-exist
requires: []
---

**Citation.**  T. Titz Mite and S. Witzel, *Non-residually finite
C2-tilde-lattices*, arXiv:2509.05054v2 (v2 of 2026-08-20; v1 September
2025), abstract, Theorem A, Corollary B, Proposition 4.3 and Appendix A
as displayed in the introduction, read from the PDF on 2026-08-22.
Corollary B is deduced there from their companion normal subgroup
theorem ([LW26, Theorem A] in their numbering).  The earlier single
example is T. Titz Mite and S. Witzel, *A C2-tilde-lattice that is not
residually finite*, arXiv:2310.03662.  Property (T) is asserted in
Theorem A itself for the uniform lattices and passes to the finite-index
subgroups `Gamma^`.

**Derivations.**  `Gamma = pi_1(Y)` acts on the universal cover `X` by
deck transformations: freely, and cocompactly since `Y` is a finite
complex.  `X` is a connected non-positively curved chamber complex, so
by Cartan--Hadamard (their Theorem 2.1) it is CAT(0) and contractible.
A group acting freely and cocompactly on a contractible, locally finite,
finite-dimensional complex is of type `F`, hence torsion-free (finite
cohomological dimension) and finitely presented, and satisfies

```text
H^k(Gamma, Z Gamma) = H^k_c(X)                                      (TW1)
```

(Brown, *Cohomology of Groups*, Ch. VIII: cohomology with group-ring
coefficients of a group of type F equals the compactly supported
cohomology of any free cocompact contractible model).  All of this
passes to the finite-index subgroups `Gamma^` (free restriction of a
free action, cocompact by finite index, (T) and non-residual-finiteness
by finite index and simplicity respectively; an infinite simple group is
not residually finite).
