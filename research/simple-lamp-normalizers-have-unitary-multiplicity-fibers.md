---
rg: 2
id: simple-lamp-normalizers-have-unitary-multiplicity-fibers
kind: claim
title: Simple-lamp automorphisms leave an arbitrary unitary regular-block multiplicity fiber
distinct_from:
  diagonal-normalizer-rigidity: that proves normalizers of a full diagonal masa are monomial; the left-regular simple-lamp algebra is coarse and has a large right-regular/multiplicity commutant.
  finite-normalizer-star-no-go: that uses a finite packet's Plancherel trace to refute a marked swap star; this computes the full exact normalizer fiber of a regular simple-lamp packet.
  simple-lamp-hyperlinear-recovery-forces-action-sofic: that is the open global implication; this is the exact local countermodel blocking the proposed amenable-classicalization proof.
---

ESTABLISHED.  Let `K` be a finite centerless nonabelian simple group, let
`Q=K^F` for a nonempty finite set `F`, and let `lambda_Q` be the left regular
representation.  For `alpha in Aut(Q)`, write

```text
P_alpha delta_q=delta_(alpha(q)).                         (SMF1)
```

On

```text
H=ell^2(Q) tensor C^m
```

every unitary implementing `alpha` on the amplified left lamp algebra is of
the form

```text
U=(P_alpha tensor 1) C,
C in U(lambda_Q(Q)' tensor M_m).                          (SMF2)
```

Conversely every such `U` implements `alpha` exactly.  The coordinate
permutation in `(SHA3)` is therefore visible in `Ad(U)`, but the `m` regular
packet copies carry a completely arbitrary unitary fiber.

This freedom is quantitatively real.  In the product basis choose
`C=1 tensor Fourier_m`.  Then covariance has zero error, while

```text
inf_(M monomial) ||U-M||_2^2 >= 2-2/sqrt(m).              (SMF3)
```

Indeed every row of `P_alpha tensor Fourier_m` has exactly `m` nonzero
entries, each of modulus `m^(-1/2)`, so its normalized overlap with any
monomial is at most `m^(-1/2)`.

The same phenomenon is compatible with actor multiplication.  Whenever a
finite actor packet acts on `Q` through automorphisms and
`pi` is a unitary representation of that packet on `C^m`,

```text
U_a=(P_(alpha_a) tensor 1)(1 tensor pi(a))                (SMF4)
```

satisfies all actor products and lamp covariance laws exactly.  Property
`(T)` does not rule out `(SMF4)`; it is an exact representation, not an
almost-invariant vector.

Thus the Burton--Chaudkhari--Juschenko--Muliarchyk classicalization of the
amenable lamp restriction does not automatically extend equivariantly to
the actor.  It supplies a permutation basis for the lamps, but actor
normalizers can remain a bounded distance from every permutation in that
basis.  Recovering the set action needs an additional theorem on the
**multiplicity-copy action**, not merely the intrinsic permutation of the
simple direct factors.
