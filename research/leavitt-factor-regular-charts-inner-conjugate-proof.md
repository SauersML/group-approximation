---
rg: 2
id: leavitt-factor-regular-charts-inner-conjugate-proof
kind: route
title: ICC plus the matrix-unit conjugacy lemma gives an internal relative chart unitary
target: leavitt-factor-regular-charts-inner-conjugate
requires:
  - leavitt-unit-group-has-no-finite-normal-subgroup
  - leavitt-regular-atlas-hyperlinearity-criterion
---

Write `M=L(Q)` and let `tau` be its canonical trace.  The established claim
`leavitt-unit-group-has-no-finite-normal-subgroup` proves in particular that
every finite conjugacy class in `Q` is trivial.  Thus `Q` is ICC and `M` is a
finite factor.

For either chart embedding `alpha_i:A_8 -> U(M)`, the restriction of `tau` is
its regular character:

```text
tau(alpha_i(h)) = 1  if h=1,
                  0  otherwise.
```

Hence the induced maps

```text
pi_i : C[A_8] -> M
```

are faithful trace-preserving unital `*`-embeddings for the canonical group
trace.  Faithfulness can be read directly from

```text
tau(pi_i(sum_h c_h h)^* pi_i(sum_h c_h h)) = sum_h |c_h|^2.
```

It remains only the following standard finite-factor lemma, whose proof is
included because the prescribed **label-preserving** conjugacy matters here.

**Lemma.**  Let `A` be a finite-dimensional C-star algebra and let
`rho,sigma:A->M` be unital trace-preserving embeddings into a finite factor.
Then there is `u in U(M)` with `u rho(a) u^*=sigma(a)` for every `a in A`.

*Proof.*  Write `A = direct_sum_r M_(n_r)(C)` and choose matrix units
`e^r_ij`.  Since the two embeddings induce the same trace,
`rho(e^r_11)` and `sigma(e^r_11)` have equal trace.  In a finite factor,
projections of equal trace are Murray--von Neumann equivalent, so choose
`v_r` with

```text
v_r^* v_r = rho(e^r_11),
v_r v_r^* = sigma(e^r_11).
```

Put

```text
u_r = sum_i sigma(e^r_i1) v_r rho(e^r_1i),
u   = sum_r u_r.
```

The matrix-unit relations give

```text
u_r^* u_r = rho(1_r),
u_r u_r^* = sigma(1_r),
```

and different summands have orthogonal initial and final central supports.
Therefore `u` is unitary.  A second matrix-unit multiplication gives

```text
u rho(e^r_ij) u^* = sigma(e^r_ij)
```

for every `r,i,j`, hence for every `a in A`.  QED

Apply the lemma to `A=C[A_8]`, taking the `*`-isomorphism between the two
copies to be the one induced by the fixed chart labels.  The resulting
unitary is the required `W`.