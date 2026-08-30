---
rg: 2
id: finite-type-restriction-overlap-defect-proof
kind: route
title: Extract the identity coefficient and sum the orthogonal cross overlaps
target: finite-type-restriction-overlap-defect-formula
requires: []
---

Transporting first lets us work with the finite subgroups `A,B` and their
characters `alpha,beta`. Expanding the two central idempotents, the
coefficient of the identity in their product is

```text
d_rho d_sigma/(|H||K|)
 sum_(a in L) alpha(a^(-1)) beta(a).
```

Unitary finite-group characters satisfy
`alpha(a^(-1))=conjugate(alpha(a))`, so character orthogonality on `L`
turns this into the right side of `(FTO1)`. It is nonnegative because the
inner product is

```text
sum_(theta in Irr(L))
 mult(theta,Res_L alpha) mult(theta,Res_L beta).
```

For projections `p,r`, traciality and idempotence give

```text
||pr||_2^2=tau((pr)^*pr)=tau(rpr)=tau(pr),
```

so zero overlap is equivalent to `pr=0`.

For the orthogonal families, `P` and `R` are projections and

```text
tau(P)=sum_i d_i^2/|H_i|,
tau(R)=sum_j e_j^2/|K_j|,
tau(PR)=sum_(i,j) tau(p_i r_j).
```

Substitution into

```text
||P-R||_2^2=tau(P)+tau(R)-2tau(PR)
```

proves `(FTO2)`. Faithfulness of the regular trace proves the zero-defect
equivalence.

For the `D_8` example, `<J,Z>` and `<J,X>` both have order four and
intersect in `<J>` of order two. The four relevant types are
one-dimensional and their restrictions to `<J>` agree. Hence every cross
overlap is `2/(4*4)=1/8`, whereas each atom has trace `1/4`. The
displayed sums both expand to `(1-J)/2`, and the strict cross-overlap
inequality excludes every termwise equality.
