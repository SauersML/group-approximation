---
rg: 2
id: rank-two-projective-transfer-equals-hnn-nonhyperlinearity
kind: claim
title: In rank two, the dimension-free projective commutator transfer inequality is equivalent to nonhyperlinearity of the centralizer HNN group
distinct_from:
  arithmetic-hnn-nonhyperlinearity-equals-global-collapse: that proves the six-way equivalence for every n>=2 but adds the dimension-free finite-matrix inequality only for n>=3 and one diagonal denominator; this adds that inequality, and its qualitative-modulus form, in rank two for every prime and every h in A minus C, where SL_2(Z) is not perfect.
  relative-commutant-collapse-for-sl2-pair: that is the open regular-trace collapse at p=2; this proves that it is equivalent, for every prime, to the unrestricted-trace collapse and to the linear projective inequality, without deciding it.
  projective-commutant-transfer-for-arithmetic-pair: that is the open projective transfer inequality; this proves that its rank-two instance is exactly nonhyperlinearity of H, so the mu_12-twisted leaks discussed there are not additional obstructions.
  rf-perfect-pair-transfer-equals-regular-rcc: that needs perfectness and so excludes rank two; this uses the adjoint and identity-doubling tricks instead.
---

Fix a prime `p`.  Put `C=SL_2(Z)`, `A=SL_2(Z[1/p])` and

```text
H=A *_C (C x Z)=<A,t | t c t^-1=c for c in C>.
```

`A` is finitely presented.  Fix any finite presentation `A=<X|R>`, any
finite set `S` of words representing a generating set of `C`, and any word
`h` representing an element of `A` outside `C`.  With `delta`, `q` and
`e_h` defined from these data as in
`adjoint-regular-rcc-gives-projective-transfer`, the following are
equivalent.

1. `H` is nonhyperlinear.
2. In every canonical trace-preserving embedding `pi:L(A)->Q` into a
   tracial matrix ultraproduct, `pi(L(C))' cap Q=pi(L(A))' cap Q`.
3. The same commutant equality holds for **every** unitary representation
   `pi:A->U(Q)` into a tracial matrix ultraproduct, whatever its trace.
4. There is `L<infinity` such that for every `d`, every assignment
   `rho:X->U(d)` and every `U in U(d)`,

   ```text
   1-|tr([U,rho(h)])|^2
    <= L(sum_(s in S)(1-|tr([U,rho(s)])|^2)+delta(rho)).   (R2T1)
   ```

5. There are `K<infinity` and a function `eta` with `eta(delta)->0` as
   `delta->0` such that every assignment and unitary satisfy

   ```text
   1-|tr([U,rho(h)])|^2
    <= K sum_(s in S)(1-|tr([U,rho(s)])|^2)+eta(delta(rho)).  (R2T2)
   ```

In particular the rank-two instance of
`projective-commutant-transfer-for-arithmetic-pair`, for any prime, any
`h` outside `SL_2(Z)` and any finite presentation, has exactly the truth
value of nonhyperlinearity of `H`; its truth value does not depend on `h`,
`S` or the presentation.  Together with
`arithmetic-hnn-nonhyperlinearity-equals-global-collapse` this also makes
it equivalent, for `p=2`, to
`relative-commutant-collapse-for-sl2-pair`.

A projective leak whose source scalars form a nontrivial character of
`C` (necessarily of order dividing `12`, since the abelianization of
`SL_2(Z)` is `Z/12`) violates `(R2T2)`, and the adjoint construction of the
cited general route converts it into an untwisted regular-trace leak.  So
in rank two no separate analysis of `mu_12`-twisted leaks is needed: any
sequence of finite-dimensional assignments carrying such a twisted leak
already makes `H` hyperlinear.

None of the five assertions is established or refuted here.
