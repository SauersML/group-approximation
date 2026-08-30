---
rg: 2
id: stw83-canonical-circle-type-i-test-proof
kind: route
title: Combine the primitive strata, shadow invariant, and dimension-two bound
target: stw83-canonical-circle-is-sharp-type-i-dimension-test
requires:
  - stw83-canonical-circle-primitive-spectrum-independent-of-n
  - stw83-canonical-circle-toeplitz-dimension-two-bound
  - stw81-continuous-trace-shadow-invariant
  - stw81-ctdim-equals-type-i-topological-dimension
---

The primitive-spectrum computation gives a type-I algebra with two
continuous-trace composition strata.  The open stratum is Morita equivalent
to `C(T)), and the closed quotient stratum is `C(T)).  Both spectra have
covering dimension one.  Therefore the definition of `ctdim`, together
with its equality with Brown--Pedersen topological dimension on separable
type-I algebras, gives

```text
ctdim(A_N)=topdim(A_N)=1.
```

The lower bound is also visible directly from the circle quotient.  The
shadow-invariant theorem says `ctdim(A_N)<=1` is equivalent to the
hereditary commutative-shadow hypothesis in Problem LXXXI.  The
coefficient-valued Toeplitz construction supplies the independent finite
bound

```text
1<=dim_nuc(A_N)<=2.
```

If Problem LXXXI is positive, its conclusion places this finite value in
`{0,1}`; the circle quotient excludes zero, so it is one.  Conversely, a
value of two gives a separable type-I counterexample satisfying the shadow
hypothesis, proving the stated reverse implication.

Finally, the two usual exact formulas are unavailable.  A continuous-trace
algebra has Hausdorff primitive spectrum, whereas the primitive-spectrum
computation shows that the closure of every point in the open circle
contains the entire closed circle.  Also, subhomogeneity passes to ideals,
but `K tensor C(T)` has the evaluation representations on an
infinite-dimensional Hilbert space and is not subhomogeneous.  Thus applying
either formula would silently add a false hypothesis.
