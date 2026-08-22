---
rg: 2
id: fixed-rectangular-kernel-return-factorization-is-impossible
kind: claim
title: A fixed rectangular kernel cannot be an unnamed return carrier for an infinite-order word
invalidates:
  - unnamed-return-via-fixed-rectangular-kernel
distinct_from:
  universal-block-return-violates-the-regular-firewall: that uses cyclicity for two fixed products and a named positive exit projection; this treats a genuinely model-dependent kernel projection and uses von Neumann rank-nullity plus injectivity of the regular infinite-order shift.
  fixed-rank-index-authenticator-has-gap-or-functoriality: that gives the gapless-versus-functional-calculus dichotomy for reading the rank of one fixed block; here rectangularity supplies the kernel density without a spectral gap, but a fixed algebraic return factorization is itself impossible.
  unnamed-fixed-space-wandering-promotion: that is the live target permitting an arbitrary model-dependent carrier; this rules out only the most direct fixed rectangular-pencil implementation and leaves matrix-dependent or growing decoders open.
---

Let `Gamma` be a group, let `w in Gamma` have infinite order, and fix
integers `p>q`.  There do not exist matrices

```text
A in M_(q,p)(C[Gamma]),       C in M_(p,q)(C[Gamma])
```

such that

```text
I_p tensor (w^2-1)=C A in M_p(C[Gamma]).               (FRK1)
```

Indeed, evaluate in the left regular representation.  The rectangular
operator

```text
lambda(A):l2(Gamma)^p -> l2(Gamma)^q
```

has Murray--von Neumann kernel dimension at least `p-q`.  Equation `(FRK1)`
makes this kernel a subspace of

```text
ker(I_p tensor (lambda(w^2)-1)).                       (FRK2)
```

But `lambda(w^2)-1` is injective when `w` has infinite order: on each left
coset of `<w^2>` it is the bilateral-shift difference on `l2(Z)`, which has
no nonzero fixed vector.  Thus `(FRK2)` has zero kernel, a contradiction.

This is exactly the fixed-pencil version of the proposed unnamed
Hilbert-hotel decoder.  In a `d`-dimensional approximate representation,
`A(U):C^(pd)->C^(qd)` always has a kernel of dimension at least `(p-q)d`.
If `(FRK1)` were a fixed consequence of the presentation, evaluation on its
kernel projection `P_U` would give

```text
tr_(pd)(P_U)>=(p-q)/p,
||(I_p tensor (w(U)^2-1))P_U||_(2,pd)=o(1).            (FRK3)
```

The carrier in `(FRK3)` is completely unnamed and may move with `U`; no
spectral gap for `A(U)^*A(U)` is needed.  Thus rectangular rank-nullity really
would bypass the hard-kernel discontinuity.  The obstruction occurs one step
later: a bounded-area, fixed group-algebra factorization proving the return
would also hold in the regular finite factor and is algebraically
inconsistent with infinite order.

Consequently `unnamed-fixed-space-wandering-promotion` cannot be obtained
from one fixed rectangular matrix pencil whose entire kernel is killed by a
fixed relator factorization.  A surviving rank-nullity construction must make
at least one of the following genuinely nonfunctorial:

- the pencil itself depends on the finite matrix coordinates;
- the family of rectangular blocks grows with dimension; or
- the return estimate is inferred only after a matrix-only selection and is
  not a fixed factorization over `C[Gamma]`.

A nontracial Hilbert-hotel representation does not evade this statement.
It may contain proper isometries, but it cannot make `(FRK1)` compatible with
an infinite-order `w`, because the same algebraic equality is automatically
visible in the faithful regular representation.

## Finite-packet corollary

Exactifying one fixed finite packet does not evade the theorem.  Its Fourier
projections and matrix units are fixed elements of a matrix algebra over
`C[Gamma]`.  Hence any **fixed-size** rectangular pencil assembled from
those coefficients and finitely many ambient words is an `A` of the form
above after one fixed matrix amplification.  If a bounded packet calculation
proves that the whole kernel is returned, its zero-defect calculation gives
the corresponding factorization (or, more generally, the same kernel
inclusion) in the regular packet corner.  Murray--von Neumann rank-nullity
then gives the identical contradiction.

Thus allowing the kernel projection itself to wander removes the need to
name a carrier, but does not remove the need for a matrix-only **decoder**.
Fixed signed-Hecke blocks, fixed semisimple packets, and a bounded menu of
rectangular Fourier corners remain on the tracial side of the firewall.  A
successful finite-packet Hilbert hotel must activate an unbounded family or
make its coefficient choice depend on the finite multiplicity coordinates.
