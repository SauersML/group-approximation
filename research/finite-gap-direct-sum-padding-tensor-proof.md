---
rg: 2
id: finite-gap-direct-sum-padding-tensor-proof
kind: route
title: Equalize dimensions, pad phases, and tensor the common table
target: elementwise-mf-corner-gaps-assemble-regular-trace
requires: []
---

Choose a common multiple `D` of `d_0,...,d_m` and replace each `phi_i` by
the direct sum of `D/d_i` identical copies.  Normalized traces, operator
defects, and the separations `(EGA2)` are unchanged.  Form the equal-weight
direct sum

```text
U(g)=direct_sum_(j=0)^m phi_j(g),
t_i=tr(U(g_i)).                                             (1)
```

Every normalized unitary trace has real part at most one.  The designated
`i`-th summand and `(EGA3)` therefore give

```text
Re t_i <= 1-c_i/M.                                         (2)
```

Direct sums take the maximum of the block operator norms, so `U` still has
defect at most `delta`, and its base block preserves `(EGA2)`.

Now add an identity block of the same dimension:

```text
U'(g)=U(g) direct_sum I,             z_i=tr(U'(g_i))=(1+t_i)/2.
                                                                  (3)
```

This keeps the same defect and norm separation.  It also makes the trace
gap insensitive to scalar phase.  Since `|t_i|<=1`, equation `(2)` gives

```text
|z_i|^2
 =(1+2 Re t_i+|t_i|^2)/4
 <=1-c_i/(2M),
|z_i|<=exp(-c_i/(4M)).                                    (4)
```

Define the final table by the diagonal tensor power

```text
Phi_p(g)=U'(g)^(tensor p).                                (5)
```

For unitaries, tensor telescoping gives

```text
||A^(tensor p)-B^(tensor p)||_op<=p||A-B||_op,            (6)
```

so `(5)` has defect at most `p delta`.  Normalized trace is multiplicative,
and `(4)` yields

```text
|tr(Phi_p(g_i))|=|z_i|^p<=exp(-p c_i/(4M)).              (7)
```

Finally, `U'(g_i)` contains both the base block `phi_0(g_i)` and a literal
identity block.  If `lambda` is an eigenvalue of the base block with
`|lambda-1|>=alpha_i`, then the tensor spectrum in `(5)` contains

```text
lambda * 1 * ... * 1.
```

Consequently `||Phi_p(g_i)-I||_op>=alpha_i`.  Equations
`(6)--(7)` prove `(EGA4)`, and the parameter choice `(EGA5)` follows
immediately.
