# XCIII: no-go audit for abstract centralization of ambient commutators

## Candidate moves tested

Starting with the ambient Powers--Dixmier identity

```text
h ~= sum_j(x_j*x_j-x_jx_j*)
```

in the full ultrapower, three natural promotions were tested:

1. average each factor over fixed free-group words;
2. place conjugate factors in orthogonal central Z-corners; and
3. invoke a finite algebraic factorization lemma which preserves the total
   self-commutator sum while forcing the factors into the relative
   commutant.

Fixed-word conjugation preserves the total sum after averaging because `h`
is central, but it only makes a larger equivariant family of factors.  It
does not make any individual factor central.  Encoding that family in
orthogonal central blocks preserves the self-commutator identity, but the
operator norm of the commutator becomes the maximum of the block defects,
not their average.  Thus the Hilbert-space cancellation behind tracial
spectral gap has no norm analogue in this construction.

## Matrix-ultraproduct countermodel

Let

```text
M=product_omega M_(n_k),          n_k->infinity,
```

and let `p=[(p_k)]` for rank-one projections `p_k`.  Uniform matrix Dixmier
averaging makes `M` uniquely traced.  Set

```text
B=C*(1,p),       D_0=M intersect B',       I_0=J_tau intersect D_0.
```

Then `p in I_0`, the first summand of

```text
D_0=pMp direct_sum (1-p)M(1-p)
```

is `Cp`, and the corresponding summand trace has value one at `p`.
Therefore `p` is not a norm limit of self-commutators with factors in
`D_0`.  But `M` has a unique trace and `tau(p)=0`, so Cuntz--Pedersen puts
`p` in the ambient closed self-commutator space.

Moreover `D_0/I_0` is the tracial matrix ultraproduct, a II_1 factor: every
ambient representative can be made block diagonal at a normalized
`2`-norm cost tending to zero because `p_k` has rank one.

This simultaneously retains:

- unique trace and uniform Dixmier averaging in the ambient norm
  ultraproduct;
- realization as a relative commutant;
- ambient self-commutator generation of the trace kernel; and
- a II_1-factor tracial quotient.

Yet relative-central self-commutator generation fails.

The dimension-independent uniform averaging used here is the von Neumann
algebra case of Archbold--Robert--Tikuisis,
[*The Dixmier property and tracial states for C*-algebras*](https://arxiv.org/abs/1611.08263).

## Exact lesson for XCIII

No finite-factorization lemma based only on the four preceding properties
can close the XCIII trace hinge.  Central Z-blocks also cannot help merely
by orthogonal assembly, because block norms take maxima.

The countermodel has one precise defect absent from XCIII: the defining
algebra `B` contains the trace-zero projection `p`, so the ambient trace is
not faithful on `B`.  In the actual problem the diagonal copy of
`A=C*_r(F_2) tensor Z` is faithfully traced, and its free-group von Neumann
factor is full.  Any successful promotion must use those facts to control
the moving averaging unitaries on the support of `h`; neither ambient
uniform Dixmier averaging nor factorization algebra alone can do so.
