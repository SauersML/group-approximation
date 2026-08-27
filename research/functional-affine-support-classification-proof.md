---
rg: 2
id: functional-affine-support-classification-proof
kind: route
title: Project the graph and apply ternary closure to the function values
target: functional-support-is-affine-exactly-on-an-affine-domain-map
requires:
  - tailored-gap-is-lcs-or-has-a-nonaffine-edge
  - cmps-copying-is-support-neutral
---

If `E` is affine, its first-coordinate projection `D` is affine.  For any
`a,b,c in D`, ternary closure of `E` gives

```text
(a+b+c, f(a)+f(b)+f(c)) in E.
```

The graph property forces
`f(a+b+c)=f(a)+f(b)+f(c)`, which is the affine-map criterion over `F_2`.
Conversely, an affine domain and affine map have an affine graph.  Applying
the same argument to the affine hull of a subgraph proves the support-level
statement.

When `D=F_2`, every subset and every map on the two-point domain obeys the
ternary criterion, proving the binary projection specialization.  The
all-affine-edge conclusion is exactly the parity presentation in
`tailored-gap-is-lcs-or-has-a-nonaffine-edge`.

In the CMPS dummy/smooth-label construction, the answer labels include
copies of satisfying 3SAT clause assignments.  The copying-support theorem
shows that an unsafe positive clause support is not deleted before those
labels are formed.  A full proper-clause domain is `F_2^3` minus one point
and fails ternary closure, so its Cartesian products are nonaffine as well.
An affine coordinate projection cannot make the full graph affine because
its first-coordinate projection is that nonaffine domain.

