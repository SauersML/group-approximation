---
rg: 2
id: free-subdirect-products-have-one-word-mf-reflections
kind: claim
title: Every finitely generated free subdirect product has a one-word internal MF reflection
root: true
artifacts:
  - research/free-subdirect-one-word-reflection-proof.md
---

Let

```text
S<=F_(r_1) x ... x F_(r_m)                              (FSP1)
```

be a finitely generated subgroup whose projection onto every factor is
surjective.  Then the binary Leavitt unit group `U` contains a finitely
generated non-MF subgroup `K_S` and a split epimorphism

```text
pi_S:K_S->>S                                            (FSP2)
```

such that

```text
Rad_MF(K_S)=ker(pi_S)=normalClosure_(K_S)(delta_S)       (FSP3)
```

for one explicit involution `delta_S`.

The group `S` is torsion-free, characteristic-zero linear, and residually a
finite `p`-group for every prime `p`.  For every prime simultaneously, the
kernel in `(FSP3)` is the finite-`p` residual.  It is also the finite,
nilpotent, solvable, compact, finite-dimensional unitary, all-field linear,
and MF residual, and

```text
ker(pi_S)=intersection_j lowerCentral_j(K_S)
         =intersection_j derived_j(K_S).                (FSP4)
```

The quotient map induces canonical isomorphisms on the profinite, pro-`p`
for every prime `p`, pronilpotent, prosolvable, and Bohr completions.  It also
identifies the complete finite-index subgroup lattices with indices, cores,
and conjugacy, and induces natural bijections

```text
Hom(S,M)~=Hom(K_S,M)                                    (FSP5)
```

for every MF, finite, compact, finite-dimensional unitary, and all-field
finite-dimensional linear target.

For every normal subgroup `N` of `K_S`,

```text
cl_MF^(K_S)(N)=pi_S^(-1)(cl_MF^S(pi_S(N))).             (FSP6)
```

Both `S` and `K_S` have decidable word problem.  Thus this construction
realizes the entire class of finitely generated free subdirect products as
exact visible quotients while concentrating every classical invisible core
in one normally generating involution.
