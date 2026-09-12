---
rg: 2
id: finite-inclusion-free-compressor-proof
kind: route
title: Insert long basis markers around prescribed quotient lifts
target: finite-inclusion-is-free-self-compressor-quotient
requires: []
---

Choose `r` and lists

```text
b_1,...,b_r in B,                 a_1,...,a_r in A
```

which generate `B` and `A`, respectively; pad either list by identities.
Let

```text
F=F(x_1,...,x_r),                 theta(x_i)=b_i.
```

Choose reduced words `R_i in F` with `theta(R_i)=a_i`, and put

```text
L=max_i |R_i|.
```

Let `e` be the exponent of `B`.  Choose a multiple `M` of `e` with `M>L`,
and later enlarge it once more if necessary.  Define

```text
alpha(x_i)=x_i^M R_i x_i^M.                             (FQP1)
```

Because `b_i^M=1`,

```text
theta(alpha(x_i))=a_i,
```

so the image of `alpha(F)` under `theta` is exactly `A`.

It remains to check that `alpha` is injective.  After freely reducing
`alpha(x_i)`, its initial and terminal blocks are positive powers of `x_i`
of length at least `M-L>0`.  The reduced word for `alpha(x_i)^(-1)` similarly
starts and ends in negative powers of `x_i`.  Consider a freely reduced word

```text
w=x_(i_1)^(epsilon_1) ... x_(i_s)^(epsilon_s).
```

At a junction between two substituted factors, distinct indices give
different boundary letters and hence no cancellation.  Equal indices in a
freely reduced source word have equal signs, so their boundary powers also
have the same sign and again do not cancel.  Thus every substituted factor
retains a nonempty boundary marker in the reduced product.  In particular
`alpha(w)` is nonempty whenever `w` is nonempty, proving injectivity.  The
same calculation gives the explicit bound

```text
|alpha(w)| >= 2(M-L)|w|,                               (FQP2)
```

after writing `w` letter by letter.

Finally, on abelianization the matrix of `alpha` is

```text
2M I_r+C,
```

where `C` is the fixed exponent-sum matrix of the words `R_i`.  Its
determinant is a degree-`r` polynomial in `M` with leading term `(2M)^r`.
After choosing the multiple `M` sufficiently large, its absolute value is
greater than one.  Hence `alpha` is not surjective and is a proper
endomorphism.

The standard normal-form theorem for ascending HNN extensions of injective
endomorphisms embeds `F` in `E` and identifies `tFt^(-1)` with `alpha(F)`.
Finally, choose a finite presentation of the finite group `B` on the
generators `b_i`, adding dummy generators if necessary.  The lifted finite
relator list normally generates `ker(theta)`.

For `(FQS1b)`, a reducing carrier commutes with every `sigma(h)`, so every
conjugate of every `r_j^(+-1)` acts trivially on it.  Products give the whole
normal closure.  For `(FQS1c)`, telescope the product of conjugates.  In one
term, commuting `E` past `sigma(h_l)^*` costs at most
`2||[E,sigma(h_l)]||_2`, since `||sigma(r)-1||<=2`; the remaining term is the
displayed normal-relator error.  Summing proves the estimate and completes
all assertions in `(FQS1)--(FQS2)`.
