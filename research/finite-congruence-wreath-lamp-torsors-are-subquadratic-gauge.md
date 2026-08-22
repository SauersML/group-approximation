---
rg: 2
id: finite-congruence-wreath-lamp-torsors-are-subquadratic-gauge
kind: claim
title: Exact finite congruence-wreath lamp torsors are gauge with subquadratic class count
distinct_from:
  coset-wreath-microstates-carry-excess-entropy: that asks for a macroscopic family of full approximate wreath models modulo global conjugacy; this proves the natural exact finite-congruence/multiplicity source of such a family has only subquadratic discrete moduli.
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that counts rational multiplicity points for a fixed finite packet to rule out an HS gap; this counts unitary-equivalence classes of full finite wreath representations and isolates the apparent continuous lamp torsor as one global-conjugacy orbit.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs compatible restriction multiplicities on a finite graph of packet groups; this imposes the whole finite wreath multiplication table and all mixed regular moments, which collapse the extension data to the regular representation.
---

Let `H=A rtimes Q` be any finite wreath packet, where `A=C_2^F` is a
finite lamp group and `Q` is a finite congruence/actor packet permuting `F`.
An exact representation `rho:H->U(d)` whose normalized character is the
canonical regular character satisfies

```text
rho is unitarily equivalent to k lambda_H,      d=k|H|. (FCW1)
```

Indeed character orthogonality says the multiplicity of
`tau in Irr(H)` is

```text
<d delta_e,chi_tau> = (d/|H|) dim(tau),                (FCW2)
```

so integrality forces `(FCW1)`.  Thus the full exact regular packet has one
unitary-equivalence class.  Every continuous choice of joint lamp
eigenbasis, packet intertwiners, or congruence-commutant coordinates lies on
that class's global `U(d)` orbit and disappears in microstate space modulo
global conjugacy.

The lamp-only calculation shows where the misleading quadratic count enters.
If `|A|=s` and all nontrivial lamp products have trace zero, the `s` joint
character spaces have equal dimension `m=d/s`.  Before quotienting, their
embeddings form the homogeneous space

```text
U(d)/(product_(chi in A-hat) U(m)),                     (FCW3)
```

of real dimension `d^2-d^2/s`.  But `(FCW3)` is exactly one global-conjugacy
orbit.  After fixing it to the standard diagonal form, actor extensions are
block-monomial.  Imposing the finite actor multiplication table turns their
block gauges into an honest representation of the finite stabilizer/little
groups; modulo the residual block-diagonal gauge, only discrete irreducible
multiplicities remain.  Imposing the mixed regular character specializes
those multiplicities to `(FCW2)`.

Even without the regular-character specialization, the number of
unitary-equivalence classes of `d`-dimensional representations of a finite
group `H` is at most

```text
(d+1)^r,                 r=|Irr(H)|<=|H|.               (FCW4)
```

For a sequence of exact regular finite packets `H_d`, `(FCW1)` implies
`|H_d|<=d`; hence

```text
log(number of classes) <= d log(d+1)=o(d^2).            (FCW5)
```

The same bound applies to extensions of a fixed congruence restriction,
because quotienting by all global conjugacies is coarser than quotienting by
the restriction commutant.  Therefore the macroscopic dimension of
`U(rho(Lambda)')` does not by itself give `c d^2` non-conjugate wreath
models: its continuous directions are basis/intertwiner gauge once the full
finite packet and mixed moments are retained.

This is a sharp no-go only for the exact finite-packet architecture.  A true
excess-entropy witness must exploit approximate models at levels where the
defect is not uniformly correctable to the growing finite wreath table, or
retain relative lamp/base moduli that cannot be absorbed by one global
conjugation.  Counting a congruence commutant or a lamp eigenbasis before the
global quotient cannot prove positive 1-bounded entropy.
