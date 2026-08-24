---
rg: 2
id: finite-packet-multiplicity-certificates-detect-mf-radicals
kind: claim
title: Finite packet multiplicity certificates detect elements of the MF radical
root: true
artifacts:
  - research/finite-packet-multiplicity-certificates-detect-mf-radicals-proof.md
---

Let `G` be countable and fix finitely many finite subgroups
`F_1,...,F_t<=G`, together with finitely many subgroup inclusions and
conjugacies among them.  For a norm-corona homomorphism

```text
rho:G->U(Q_d),
```

write `mu_(a,pi)` for the eventual coordinate multiplicity germ of the
irreducible representation `pi in Irr(F_a)` inside `rho|_(F_a)`.

The following constraints are exact integer linear relations among the
`mu_(a,pi)`:

1. restriction along `F_a<=F_b`, using the ordinary irreducible restriction
   multiplicities;
2. transport along `gF_ag^(-1)=F_b`, using the induced bijection of
   irreducible types;
3. refinement through an intermediate finite subgroup;
4. orthogonal sums and central spectral cuts inside the finite packet
   algebras.

Collect any finite family of these constraints in an integer matrix `B`.
For a selected type `(a,pi)`, a rational identity

```text
-e_(a,pi)=B^T y+s,
y rational,  s>=0 rational,                              (FPM1)
```

forces

```text
mu_(a,pi)=0                                              (FPM2)
```

in every norm-corona representation of `G`.

Now let `z in F_a`.  If certificates `(FPM1)` exist for every
`pi in Irr(F_a)` with `pi(z)!=1`, then

```text
rho(z)=1
```

for every norm-corona representation `rho`, and therefore

```text
z in Rad_MF(G).                                          (FPM3)
```

If finitely many packet elements certified in this way normally generate
`G`, then `G` has full MF radical.

The test is finite and exact: all input consists of finite character tables,
integer restriction matrices, permutation matrices from conjugacy, and a
rational dual vector.  Failure of the dual certificate produces a compatible
nonzero integer multiplicity assignment, proving that the chosen finite
packet constraints alone do not annihilate that type.

For elementary groups over torsion coefficient rings, finite additive root
windows and three-root Heisenberg windows supply the packets.  Their
restriction matrices record addition and multiplication simultaneously, so
the same certificate calculus can combine several finite coefficient windows
without reconstructing a global coefficient representation.
