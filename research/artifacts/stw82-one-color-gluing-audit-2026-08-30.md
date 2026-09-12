---
rg: 2
title: STW LXXXII one-colour gluing audit (2026-08-30)
kind: artifact
---

# Scope

This audit isolates the local step required to reuse a quotient colour and
an ideal colour in the standard quasicentral-cut proof of the extension
estimate for nuclear dimension.  It does not claim the maximum formula in
generality.

# Exact direct-sum criterion

For cpc order-zero maps `alpha:F->B` and `beta:G->B`, the direct-sum map
`(x,y) |-> alpha(x)+beta(y)` is order zero exactly when
`alpha(1)beta(1)=0`.  This follows by testing the two unit elements for the
necessary direction and using the supporting-homomorphism description for
the sufficient direction.  Mere commutation of the ranges is insufficient.

# Quantitative perturbation barrier

The standard two cuts have unit supports `h` and `1-h`.  If orthogonal
positive contractions `a,b` approximate them within `delta`, then

```text
norm(h(1-h)) <= 2 delta.
```

Conversely, if `eta=norm(h(1-h))<1/4`, spectral functional calculus gives
`p=chi_[1/2,1](h)` and

```text
norm(h-p) <= (1-sqrt(1-4 eta))/2.
```

Hence asymptotic orthogonalizability of the complementary unit supports is
equivalent to asymptotic projectionality of the cutdown.  Approximate
centrality controls commutators only; it does not control this overlap.

# Stress test: the interval extension

In

```text
0 -> C_0((0,1)) -> C([0,1]) -> C directSum C -> 0,
```

every positive contractive approximate unit of the ideal is central, but
continuity forces it to take the value `1/2` eventually.  Consequently its
overlap norm is exactly `1/4` at every sufficiently late stage.  The maximum
formula nonetheless holds, with dimensions `1,1,0`.

This example separates two assertions that a gluing argument must not
conflate:

1. the nuclear-dimension maximum formula can hold;
2. the two raw complementary cutdowns can be merged into one order-zero
   colour by a small perturbation.

The second fails maximally in this example.  Any route to the general
formula must therefore alter the approximating maps, subdivide or absorb
the transition region, or obtain orthogonality from structure other than
quasicentrality.

# AF-coefficient Toeplitz replacement

There is now a separable nonquasidiagonal class where the transition region
is replaced coherently rather than cut projectionally.  Let `A` be a nonzero
unital AF algebra and tensor the index-`N` Toeplitz extension with `A`:

```text
0 -> K tensor A -> C*(S^N,K) tensor A
  -> C(T) tensor A -> 0.
```

At a finite-dimensional AF stage `A_j=directSum_l M_(n_l)`, the middle
algebra is a finite direct sum of matrix amplifications of the scalar
index-`N` Toeplitz algebra.  Its established two-colour approximation already
absorbs the transition band.  Passing through the injective AF limit gives
middle nuclear dimension at most one.  The quotient has dimension exactly
one, while the ideal is AF, so the dimensions are `0,1,1`.

This is not hidden raw-cut reuse.  The six-term boundary sends the exterior
product of the circle generator with `[1_A]` to `+-N[1_A]`, which is nonzero
in the torsion-free dimension group `K_0(A)`.  The extension is therefore not
quasidiagonal and cannot have a projectional quasicentral approximate unit.
The finite-stage Toeplitz maps replace the transition approximation instead
of perturbing its complementary supports.

# Trust boundary

The operator-algebra calculations above are elementary except for the
standard supporting-homomorphism theorem for order-zero maps and the
standard equality between nuclear dimension of a commutative C*-algebra and
covering dimension.  No literature result is used as an input to a claimed
solution of STW Problem LXXXII.
