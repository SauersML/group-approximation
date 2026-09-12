---
rg: 2
id: stw11-folner-capacity-faithful-trace-proof
kind: route
title: Turn positive maximal orbit averages into a countable faithful mixture
target: stw11-folner-capacity-faithful-trace-criterion
requires:
  - tww-gabe-schafhauser-af-embedding-theorem
artifacts:
  - research/artifacts/stw11-folner-capacity-audit-2026-08-30.md
---

Write the action on functions as

```text
alpha_g(f)(x)=f(g^(-1)x).
```

## 1. Invariant measures give the lower variational bound

If `mu` is any invariant probability measure and `f` is positive, then

```text
mu(f)=mu(A_N(f)) <= ||A_N(f)||
```

for every `N`.  Taking first the maximum over the compact invariant-measure
simplex and then the lower limit gives

```text
max_mu mu(f) <= liminf_N ||A_N(f)||.                        (FC3)
```

In particular, a faithful invariant measure forces `(FC1)`.

## 2. Maximizing orbit segments give the upper bound

Fix `f in C(X)_+` and let

```text
c=limsup_N ||A_N(f)||.
```

Choose `N_j -> infinity` and `x_j in X` such that

```text
A_(N_j)(f)(x_j) -> c.
```

Form the empirical orbit measures

```text
nu_j=|F_(N_j)|^(-1) sum_(g in F_(N_j)) delta_(g^(-1)x_j).
```

Compactness of the probability-measure space gives a weak-star convergent
subsequence, with limit `mu_f`.  The Følner boundary estimate gives, for
every fixed `h in Z^d`,

```text
||h_*nu_j-nu_j||
 <= |hF_(N_j) symmetric_difference F_(N_j)|/|F_(N_j)| -> 0.
```

Thus `mu_f` is invariant.  Moreover

```text
mu_f(f)=lim_j nu_j(f)=lim_j A_(N_j)(f)(x_j)=c.             (FC2)
```

Hence `c<=max_mu mu(f)`.  Together with `(FC3)`, this proves `(FC0)`;
in particular the apparent limsup is an actual limit.  If `(FC1)` holds,
then `(FC2)` supplies an invariant probability measure detecting `f`.

## 3. Countably many detecting measures give one faithful measure

Choose a countable base `(U_k)` of nonempty open subsets of `X`, and choose
nonzero `f_k in C(X)_+` supported in `U_k`.  Step 2 supplies invariant
probability measures `mu_k` with `mu_k(f_k)>0`.  Set

```text
mu=sum_(k=1)^infinity 2^(-k) mu_k.
```

This norm-convergent convex series is an invariant probability measure.  If
`U` is nonempty and open, choose `U_k subset U`; then

```text
mu(U) >= 2^(-k) mu_k(U_k) > 0.
```

Consequently `mu` has full support, equivalently it is faithful on `C(X)`.
This proves the converse implication.

## 4. Dense minimal points imply the criterion

Assume the union of minimal closed invariant subsets is dense.  Given a
nonempty open `U`, choose a minimal invariant compact set `Y` meeting `U`.
Amenability of `Z^d` gives an invariant probability measure on `Y`.  Its
support is a nonempty closed invariant subset of `Y`, hence equals `Y` by
minimality, and therefore the measure gives positive mass to `U`.

Apply this to a countable base and take the same weighted sum as in Step 3.
The resulting invariant probability has full support.  By Step 1 it also
verifies `(FC1)`.

## 5. Pass to the crossed product

Let `E:C(X) rtimes_r Z^d -> C(X)` be the canonical expectation.  It is
faithful, and invariance makes `tau=mu E` a trace.  Faithfulness of `mu` and
`E` makes `tau` faithful.  The crossed product is separable and nuclear, and
the amenable transformation groupoid satisfies the UCT.  Hence `tau` is an
amenable trace and the TWW--Gabe--Schafhauser AF-embedding theorem embeds the
crossed product into a unital simple AF algebra.  Since `Z^d` is amenable,
the full and reduced crossed products agree.
