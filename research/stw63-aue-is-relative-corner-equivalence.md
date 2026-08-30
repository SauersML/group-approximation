---
rg: 2
id: stw63-aue-is-relative-corner-equivalence
kind: claim
title: Approximate unitary equivalence is exact relative-corner equivalence
---

Let `A` be a separable unital C-star algebra, let `B` be any unital C-star
algebra, let `phi,psi:A->B` be unital star
homomorphisms, and set

```text
B_infinity = ell_infinity(N,B)/c_0(N,B),
pi(a) = diag(phi(a),psi(a)),
D = M_2(B_infinity) intersect pi(A)',
p = diag(1,0),       q = diag(0,1).                    (1)
```

Then `phi` and `psi` are approximately unitarily equivalent if and only if
the projections `p` and `q` are Murray--von Neumann equivalent in `D`.

Thus the return problem has an exact, non-asymptotic formulation inside one
relative sequence algebra.  Separability of the domain is what permits one
implementing sequence rather than a net; no nuclearity or stable-rank
hypothesis is used.  In particular the statement applies to `A=Z`.
