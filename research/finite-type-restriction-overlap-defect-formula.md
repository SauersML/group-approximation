---
rg: 2
id: finite-type-restriction-overlap-defect-formula
kind: claim
title: Additive finite-type marginal equality is exactly a restriction-overlap defect
artifacts:
  - research/finite-type-restriction-overlap-defect-proof.md
distinct_from:
  finite-character-hecke-intersection-formula: that treats one-dimensional characters and pairwise orthogonality; this treats arbitrary irreducible finite types and the exact L2 defect of equality between two orthogonal sums.
  plancherel-restriction-coupling: that gives the regular restriction coupling along one subgroup inclusion; this allows arbitrary transported finite subgroups and computes the complete additive projection defect.
  canonical-full-type-overlap-is-algebraic-corner-containment: that characterizes full overlap of one source projection with one target; this permits genuinely many-to-many overlap among two projection partitions.
---

Let `H,K` be finite subgroups of a group `Gamma`, let
`rho in Irr(H)` and `sigma in Irr(K)`, and write

```text
z_(H,rho)=d_rho/|H| sum_(u in H) chi_rho(u^(-1))u.
```

For `g,h in Gamma`, put

```text
p=g z_(H,rho) g^(-1),       r=h z_(K,sigma) h^(-1),
A=gHg^(-1),                 B=hKh^(-1),
L=A intersect B,
alpha(a)=chi_rho(g^(-1)ag), beta(b)=chi_sigma(h^(-1)bh).
```

Then

```text
tau_Gamma(pr)=||pr||_2^2
 =d_rho d_sigma |L|/(|H||K|)
   <Res^A_L alpha,Res^B_L beta>_L.                       (FTO1)
```

In particular `pr=0` exactly when the two transported restrictions have no
common irreducible constituent on `L`.

More generally let `(p_i)` and `(r_j)` be finite orthogonal families of
transported central finite-type projections, and put
`P=sum_i p_i`, `R=sum_j r_j`. With the analogous intersections `L_ij`
and transported characters `alpha_i,beta_j`,

```text
||P-R||_2^2
 =sum_i d_i^2/|H_i| + sum_j e_j^2/|K_j|
  -2 sum_(i,j) d_i e_j |L_ij|/(|H_i||K_j|)
       <Res_(L_ij) alpha_i,Res_(L_ij) beta_j>.           (FTO2)
```

The canonical trace is faithful, so `(FTO2)` vanishes if and only if the
genuinely additive group-ring identity `P=R` holds. No termwise matching
of the two families is required.

For trivial types, the inner product in `(FTO1)` is always one and `L`
contains the identity. Hence two transported ordinary subgroup Reynolds
averages are never orthogonal. A nontrivial projection-valued atlas made
directly from finite subgroup types must use nontrivial character/type
sectors (or signed differences), not bare Reynolds averages.

The smallest symmetric many-to-many example is the order-eight
dihedral/Pauli group

```text
D_8=<J,X,Z | J^2=X^2=Z^2=1, J central, XZ=JZX>,
q=(1-J)/2.
```

Put

```text
p_epsilon=q(1+epsilon Z)/2,       r_delta=q(1+delta X)/2.
```

These are character idempotents of `<J,Z>` and `<J,X>`. Their subgroup
intersection is `<J>` and all four characters restrict there as
`J |-> -1`, so `(FTO1)` gives

```text
tau(p_epsilon r_delta)=1/8,       tau(p_epsilon)=tau(r_delta)=1/4.
```

Thus

```text
p_+ + p_- =q=r_+ + r_-
```

while no `p_epsilon` equals any `r_delta`: the equality is a true
`2 by 2` additive overlap, not a disguised pairing. It remains wholly
inside one finite root block and therefore does not solve the no-CE atlas;
it is the minimal local cell that a load-bearing cyclic construction must
exceed.
