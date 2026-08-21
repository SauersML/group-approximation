---
rg: 2
id: affine-nested-odd-xor-selectors-force-affine-behavior-proof
kind: route
title: Flatten the selector tree and apply ternary closure to three singleton models
target: affine-nested-odd-xor-selectors-force-affine-behavior
requires: []
---

The solution set of a finite family of affine equations over `F_2` is an
affine subspace.  Projection to a subset of coordinates preserves affinity.
Thus eliminating every internal bit of a nested selector construction leaves
an affine feasible set

```text
A subseteq F_2^Lambda
```

for the visible activation vector.  An affine set is closed under ternary
sums: if `u,v,w in A`, then `u+v+w in A`.  By branch completeness,
`e_lambda in A` for every visible label.  Hence, for three distinct labels,

```text
e_lambda+e_mu+e_nu in A.                                 (AOX3)
```

This activation has odd parity, so an outer odd-selector row does not reject
it.  Assign its three independent payload copies the values `x,y,z in B`.
All other labels are inactive.  Formula `(AOX1)` gives the decoded scalar
payload `x+y+z`.  Exact scalar soundness therefore forces `(AOX2)`.

It remains to identify the closure condition.  A nonempty set
`B subseteq F_2^n` is affine if and only if it is closed under ternary sums.
Indeed, choose `b_0 in B`.  If `B` is ternary closed, then

```text
V=B+b_0
```

contains zero, and for `u=x+b_0`, `v=y+b_0` in `V`,

```text
u+v=(x+y+b_0)+b_0 in V
```

because `x+y+b_0 in B`.  Thus `V` is a linear subspace and `B=b_0+V` is an
affine coset.  The converse follows immediately by adding three elements of a
coset in characteristic two.

Therefore, if `B` is nonaffine, choose `x,y,z in B` with
`x+y+z notin B`; `(AOX3)` produces an exact feasible scalar selector model
whose aggregate decoder is rejected by every source branch.  Refinement,
finite nesting, and vertex-local relabelling do not change the argument: after
flattening they only enlarge `Lambda` and project an affine solution set.
