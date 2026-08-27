---
rg: 2
id: kazhdan-complement-llp-does-not-weaken-full-llp
kind: claim
title: Removing the trivial Kazhdan summand does not weaken the LLP gate for minimally almost periodic Kazhdan groups
distinct_from:
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that is the open positive full-algebra target; this is an established no-gain theorem showing that deletion of the isolated trivial sector produces an equivalent target.
  simple-kazhdan-kac-moody-lattices-exist: that supplies explicit simple Kazhdan groups with no nontrivial finite-dimensional representations; this is the operator-algebraic reduction that applies to every group with those representation-theoretic properties.
---

Let `G` be an infinite discrete property-(T) group with no nontrivial
finite-dimensional unitary representations.  Let `p in C^*(G)` be the
Kazhdan projection: in every unitary representation `rho`, `rho(p)` is the
orthogonal projection onto the invariant vectors.  Put

```text
A_0 := (1-p) C^*(G),
pi_0(g) := (1-p) u_g in U(A_0).                         (KCL1)
```

**THEOREM.**

```text
(a) C^*_(pi_0)(G) = A_0,  lambda_G is weakly contained in pi_0,
    and pi_0 is a nonamenable representation.                 (KCL2)

(b) A_0 has LLP  iff  C^*(G) has LLP.                          (KCL3)
```

Consequently Paulsen--Rahaman--Samei Theorem 4.6 applied to `pi_0`
does give

```text
LLP(A_0)  =>  G is non-hyperlinear,                            (KCL4)
```

but at these groups `(KCL4)` is **exactly the old full-algebra LLP
gate**, not a weaker positive target.

**Proof.**  The Kazhdan projection is central and satisfies
`u_g p = p` for every `g`.  Hence

```text
p C^*(G) = C p,
C^*(G) = C p direct_sum (1-p) C^*(G).                          (KCL5)
```

The images `(1-p)u_g` generate the second summand, proving the first
part of `(KCL2)`.  Since `G` is infinite, the regular representation has
no invariant vector, so `lambda_G(p)=0`.  Therefore its integrated form
factors through `A_0`, which is precisely `lambda_G prec pi_0`.

Any finite-dimensional subrepresentation of `pi_0` would be trivial by
hypothesis, hence would consist of invariant vectors.  But `p` acts as
zero on `pi_0`, so no such nonzero subrepresentation exists: `pi_0` is
weakly mixing.  For a property-(T) group an amenable representation has
a nonzero finite-dimensional subrepresentation (Bekka, *Amenable
unitary representations of locally compact groups*, Invent. Math. 100
(1990), Corollary 5.9; this is the input used in
Paulsen--Rahaman--Samei arXiv:2606.18369v1, Corollary 4.7).  Thus `pi_0`
is nonamenable.

Finally LLP is preserved by unital direct summands and by finite direct
sums.  Applying this to `(KCL5)`, and using LLP of `C`, gives `(KCL3)`.
Paulsen--Rahaman--Samei Theorem 4.6 gives `(KCL4)`.

**Concrete consequence.**  The centre-free Caprace--Remy groups in
`simple-kazhdan-kac-moody-lattices-exist` are infinite, simple, finitely
generated and Kazhdan.  Every finite-dimensional unitary representation
is trivial (a finitely generated linear image is residually finite, while
an infinite simple group has no nontrivial finite quotient).  Therefore
their proper Kazhdan-complement completion `A_0` supplies no shortcut
around `triangle-relator-extension-admits-local-ucp-sections`: proving
LLP for `A_0` is equivalent to proving LLP for their full group algebra.
