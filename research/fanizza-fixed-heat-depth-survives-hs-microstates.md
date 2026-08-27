---
rg: 2
id: fanizza-fixed-heat-depth-survives-hs-microstates
kind: claim
title: Every fixed Fanizza heat depth retains its C-star bound in HS microstates
distinct_from:
  fanizza-heat-filter-has-uniform-cstar-decay: that proves the operator-norm estimate in exact representations; this transfers each fixed-depth estimate to arbitrary normalized-HS approximate representation sequences.
  fanizza-heat-filter-one-sided-return: that must compare the filtered amplitude with one fixed marked carrier; this proves only the filtered side and uses no return.
  depthwise-canonical-kleene-needs-no-uniform-runtime-gap: that is the abstract double-limit reverse-Kleene criterion; this supplies its Fanizza-specific fixed-depth analytic input.
---

**ESTABLISHED.**  Fix a NONHALT Fanizza instance `m` and its accelerated
filter

```text
B_t=D_R p_t(H_m),              A_t=B_t^*B_t.           (FHM1)
```

Let `(U_n)` be any sequence of finite-dimensional unitary tuples whose
defects tend to zero on every relator of the native recursively presented
group.  For every **fixed** `t>=1`,

```text
limsup_n ||B_t(U_n)||_2^2
 =limsup_n tr(A_t(U_n))
 <=C_m/(4t^2).                                         (FHM2)
```

No stability theorem, dimension bound, convergence rate, or canonical trace
hypothesis is required.

## Proof

If `(FHM2)` failed, pass to a subsequence on which its left side exceeds
`C_m/(4t^2)+epsilon`, and choose a free ultrafilter.  Because every fixed
relator defect tends to zero, coordinatewise evaluation induces a genuine
unitary representation `pi` of the native group in the tracial matrix
ultraproduct.  The group-algebra polynomial `B_t` has fixed finite length, so

```text
lim_U ||B_t(U_n)||_2^2=||pi(B_t)||_2^2
 <=||pi(B_t)||^2.                                      (FHM3)
```

By `fanizza-heat-filter-has-uniform-cstar-decay`, the last expression is at
most `C_m/(4t^2)` in every representation, a contradiction.

The order of quantifiers is essential.  The result says nothing for a depth
`t=t(n)` varying with matrix dimension.  It is precisely the fixed-depth
statement consumed by the depthwise canonical double limit.

