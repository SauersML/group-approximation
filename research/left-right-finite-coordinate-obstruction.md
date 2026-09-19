---
rg: 2
id: left-right-finite-coordinate-obstruction
kind: claim
title: The non-MF compression obstruction survives over left-right-finite building blocks
distinct_from:
  finite-tracial-cstar-transport: That root proposed all faithfully traced coordinates and is false; this gives a genuine sufficient subclass.
  faithfully-traced-unital-coordinates: That established bookkeeping claim supplies finite coordinates, nonzero traced corners and projection lifting; this claim adds the left-right finiteness needed for Kazhdan transport.
artifacts:
  - research/artifacts/left-right-finite-coordinate-obstruction-2026-08-19.md
  - non_mf_groups_exist.tex
---

Let `(A_n,tau_n)` be unital C-star algebras with faithful tracial states and
assume every left-right algebra `D_(tau_n)(A_n)` is finite.  Put

```text
Q_A = prod_n A_n / directSum_n A_n.
```

For every Kazhdan conjugation datum in a countable group `H`, the finite-normal
and central-sign obstruction theorems remain valid with the matrix corona
replaced by `Q_A`.  In particular, if

```text
u = [tct^-1, iota(a)],
w = u^2
```

is a nontrivial central involution, every homomorphism
`H -> U(Q_A)` maps `w` to `1`.

The class is closed under the corners used by the proof: if `q in A` is a
nonzero projection, then the left-right algebra of `(qAq,tau_q)` is a unital
C-star subalgebra of the corner

```text
(L_q R_q) D_tau(A) (L_q R_q),
```

and is therefore finite.

Concrete infinite-dimensional examples include commutative algebras with a
faithful trace and AF (hence UHF) algebras with a faithful trace.  For AF `A`,
`D_tau(A)` is an image of `A tensor A^op`; the tensor product is AF and its
quotients are AF, hence finite.
