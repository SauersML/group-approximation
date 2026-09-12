---
rg: 2
id: two-site-a5-plancherel-center-separates-mark
kind: claim
title: The rational A5 center separates the two marked lamp sites on Plancherel mass thirty-five over seventy-two
distinct_from:
  a5-center-spectrum-has-constant-one-site-hamming-gap: that computes the cost of completing a wrong site map on an already coherent finite packet; this uses only the two marked sites and supplies their canonical positive separation before any actor table has been extracted.
  finite-cylinder-mixed-traces-kill-normalizer-holonomy: that classicalizes an already exact finite transformation-group table; this produces the two-site center projections and their covariance but no finite actor table.
  simple-lamp-hyperlinear-recovery-forces-action-sofic: that asks for a complete sofic action model; this is a fixed two-site spectral statement inside arbitrary canonical microstates.
---

Let `K=A5`, let `p!=q` be two sites, and put

```text
L=K_p x K_q.
```

Let `z in C[K]` be the central primitive idempotent belonging to the
rational five-dimensional irreducible representation of `A5`, and let
`z_p,z_q in C[L]` be its two coordinate copies.  In every canonical-trace
normalized-Hilbert--Schmidt microstate sequence of a group containing `L`,
finite-group exactification gives projections `Z_(p,n),Z_(q,n)` with

```text
tr(Z_(p,n))->5/12,
tr(Z_(q,n))->5/12,
tr(Z_(p,n)Z_(q,n))->25/144.                            (TAP1)
```

Consequently the exclusive-or projection

```text
D_n=Z_(p,n)(1-Z_(q,n))+(1-Z_(p,n))Z_(q,n)             (TAP2)
```

satisfies

```text
tr(D_n)->35/72.                                        (TAP3)
```

This is a fixed positive two-site label-separation carrier.  It does not
shrink with the matrix dimension or with any actor window.

The coefficient is completely explicit.  If `C_2,C_3` denote the sums of
the order-two and order-three conjugacy classes in `A5`, then the character
values `(5,1,-1,0,0)` give

```text
z=(1/12)(5*1+C_2-C_3).                                 (TAP3a)
```

Thus every covariance estimate below is a fixed 36-word rational
calculation; no spectral choice or irrational character field is hidden in
the carrier.

Suppose an actor element `g` conjugates the lamp at `x` to the lamp at `y`,
where `x,y in {p,q}`.  If `U_(g,n)` is its microstate matrix, then

```text
||U_(g,n) Z_(x,n) U_(g,n)^*-Z_(y,n)||_2 ->0.           (TAP4)
```

The same assertion holds simultaneously for every fixed finite list of
such pair-preserving incidences.  Thus arbitrary hyperlinear microstates of
the `A5` lamp wreath already contain the separated two-valued field and all
of the covariance relations used by the marked-pair definition.

What is not supplied is a finite permutation state space on which the actor
is approximately multiplicative.  The projections in `(TAP1)--(TAP4)` may
have arbitrary unitary multiplicity fibers.  Turning this fixed two-site
field into permutation states is isolated separately as
`two-site-a5-center-classicalization`.
