---
rg: 2
id: km-lp-fails-via-development-end-cohomology
kind: route
title: Ioana-Spaas-Wiersma Corollary D through the end cohomology of the development
target: compact-hyperbolic-km-lattices-fail-lp
requires:
  - km-development-has-nonzero-end-cohomology-in-degree-one
  - km-group-ring-h2-is-development-end-cohomology
  - simple-kazhdan-kac-moody-lattices-exist
---

By `km-group-ring-h2-is-development-end-cohomology`,
`H^2(Lambda;Z Lambda)=H^1_infty(X;Z)` for the Levi-triangle development
`X` of the lattice, and the open input asserts this group is nonzero.
`Lambda` has property (T) by `simple-kazhdan-kac-moody-lattices-exist`.
Ioana--Spaas--Wiersma, arXiv:2006.01874, Corollary D (verbatim in
research/artifacts/isw-ddjmo-cr-cohomology-sources-2026-08-21.md): a
countable property (T) group with `H^2(Gamma,Z Gamma)!=0` has a full
C*-algebra without the lifting property.  Hence `C^*(Lambda)` fails LP.
