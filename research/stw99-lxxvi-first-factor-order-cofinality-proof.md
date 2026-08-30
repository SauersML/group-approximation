---
rg: 2
id: stw99-lxxvi-first-factor-order-cofinality-proof
kind: route
title: Factor a finite algebraic tensor through one first-factor row
target: stw99-lxxvi-first-factor-cu-image-is-order-cofinal
requires: []
---

Stabilize throughout and identify

```text
(A tensor_min B) tensor K ~= (A tensor K) tensor_min B.
```

Represent `x` by a positive element `a` in this algebra.  If `x'<<[a]`, the
standard cutdown property of `Cu` gives `epsilon>0` with

```text
x'<=[(a-epsilon)_+].                                     (P1)
```

Approximate `a^(1/2)` closely enough by a finite algebraic tensor

```text
z=sum_(j=1)^N alpha_j tensor b_j,
       alpha_j in A tensor K,       b_j in B,
```

that `||a-z*z||<epsilon`.  The positive-element perturbation lemma and
`(P1)` give

```text
x'<=[(a-epsilon)_+]<=[z*z].                              (P2)
```

Put

```text
R=(alpha_1 tensor 1_B,...,alpha_N tensor 1_B),
C=(1 tensor b_1,...,1 tensor b_N)^t.
```

Here the entries of `C` act as multipliers if `A` is nonunital, and `z=RC`.
Therefore

```text
zz*=R C C* R* <= ||C||^2 R R*
               = ||C||^2 (sum_j alpha_j alpha_j*) tensor 1_B.   (P3)
```

Positive domination implies Cuntz subequivalence, while `z*z` and `zz*`
represent the same Cuntz class.  With

```text
y=[sum_j alpha_j alpha_j*] in Cu(A),
```

equations `(P2)--(P3)` prove `(OC1)`.

For the global assertion, choose a rapidly increasing sequence
`x_1<<x_2<<...` with supremum `x`.  Apply `(OC1)` to obtain
`x_n<=Cu(iota)(y_n)`.  The partial sums

```text
s_n=y_1+...+y_n
```

increase in `Cu(A)`; set `y=sup_n s_n`.  Since a Cu-morphism preserves
addition and increasing suprema,

```text
x=sup_n x_n <= sup_n Cu(iota)(s_n)=Cu(iota)(y),
```

which is `(OC2)`.

**Trust boundary.**  The proof places an image element above a compactly
contained window, and then above the whole class by a countable sum.  It
does not place a nonzero image class inside the hereditary support of `x`,
does not reflect comparison, and does not approach surjectivity.
