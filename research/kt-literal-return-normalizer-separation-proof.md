---
rg: 2
id: kt-literal-return-normalizer-separation-proof
kind: route
title: Test one exterior conjugate against the edge conditional expectation
target: kt-literal-return-stays-far-from-edge-normalizers
requires:
  - marked-double-coset-infinite-degree
---

We first record a general matrix inequality.  Let `B subset M_d` be a
unital finite-dimensional C-star algebra with trace-preserving conditional
expectation `E_B`.  For unitaries `x,a`, with `a in B`, put

```text
r=||E_B(x^* a x)||_2.
```

If `w in N(B)`, then `w^*aw` is a unitary in `B`, and hence

```text
1-r
 <=||E_B(w^*aw)-E_B(x^*ax)||_2
 <=||w^*aw-x^*ax||_2
 <=2||w-x||_2.                                        (NRP1)
```

Taking the infimum over `w` proves

```text
dist_2(x,N(B)) >= (1-r)/2.                             (NRP2)
```

For the Kun--Thom return choose `delta` as in `(LRN1)`.  Fixed-word
telescoping of the presentation defects gives

```text
||x^*phi(delta)x-phi(h^(-1)delta h)||_2<=omega,
```

so contractivity of `E_B` yields

```text
r<=q_k+omega.                                         (NRP3)
```

Equations `(NRP2)--(NRP3)` prove `(LRN2)`.  Relative canonical moments give
`q_k->0` because `k notin Gamma`; multiplicativity on this one fixed word
gives `omega->0`, proving `(LRN3)`.

It remains to quantify the correction.  Since `y=x-E_B(x)` and `x` is a
unitary,

```text
||y-x||_2=s.
```

Choose a unitary polar extension `v` of `y` minimizing Frobenius distance
to `y`.  Since `x` is an admissible unitary,

```text
||v-y||_2<=||x-y||_2=s,
||v-x||_2<=2s.                                        (NRP4)
```

For every normalizer `w`, the triangle inequality and `(LRN2)` give

```text
||v-w||_2>=||x-w||_2-||v-x||_2
          >=(1-q_k-omega)/2-2s.                       (NRP5)
```

Taking the infimum proves `(LRN4)`.  Notice that the estimate is normalized,
padding-stable, and uses only one exterior conjugate.  In the exact regular
model it reduces to

```text
x=lambda(h),
x^*lambda(delta)x=lambda(h^(-1)delta h) orthogonal to B,
```

so the obstruction is intrinsic to the marked double coset rather than a
loss introduced by correction.
