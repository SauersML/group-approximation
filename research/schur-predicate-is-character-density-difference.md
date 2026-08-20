---
rg: 2
id: schur-predicate-is-character-density-difference
kind: claim
title: A Schur predicate projection is exactly a difference of two finite-group character densities
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  schur-rank-output-is-not-a-scalar-selector: that rules out reading a nonlinear rank output as one group word; this reads it as a fixed linear combination of finite-group words.
  predicate-rank-gate-doubles-restriction-multiplicity: that computes simple-module dimensions and restriction multiplicities; this packages the same jump as an exact identity in the finite group algebra.
  finite-predicate-signed-permutation-sector: that realizes predicate support in a chosen higher-dimensional block; this character-density formula is canonical for the nested Schur packet and requires no extra support representation.
---

Let `C_f=B_f^Q<=B_f` be the corrected Schur child/full-packet inclusion,
let `D=2^N`, and restrict both finite group algebras to `J=-1`. For a finite
group `H` with central sign `J`, define its negative-sector character-density
element

```text
Z_H=sum_(pi in Irr(H), pi(J)=-1) e_pi/dim(pi),          (CDF1)
```

where `e_pi` is the primitive central idempotent of `C[H]`. Regard `Z_C` as
an element of `C[B_f]`. If

```text
p_x=product_i (1+(-1)^(x_i)z_i)/2,
p_-= (1-J)/2,
P_f=p_- sum_(x:f(x)=1) p_x,
```

then the following is an exact finite group-algebra identity:

```text
Z_(C_f)-Z_(B_f)=P_f/(2D).                              (CDF2)
```

Thus every Boolean predicate projection—not merely its trace or support—is a
fixed linear combination of ordinary words from two nested finite groups.
The formula is effective because

```text
e_pi=(dim(pi)/|H|) sum_(h in H) conjugate(chi_pi(h)) h,
```

so `(CDF1)` is obtained directly from the two finite character tables.

For every exact finite-dimensional representation `rho`, normalized trace of
`Z_H` is total `H`-irreducible multiplicity divided by ambient dimension.
Consequently `(CDF2)` is exactly the linear character-theoretic form of the
Schur multiplicity surplus.

This bypasses the affine scalar-word barrier but does not by itself impose a
BCS constraint. A group compiler must still make the appropriate returned
copies of `Z_C` and `Z_B` agree, or charge their discrepancy, using finitely
many ordinary relators. The advantage is that the object to return is now an
explicit fixed finite sum of group words rather than an unnamed module count.
