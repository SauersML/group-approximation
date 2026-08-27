---
rg: 2
id: unitary-corner-compressions-force-reduction
kind: claim
title: A unitary compression of a unitary already lies on a reducing corner
invalidates:
  - halmos-literal-dilation-groupifies-nonru-bcs
distinct_from:
  involution-hecke-corner-has-no-proper-literal-projections: that uses canonical Fourier coefficients to classify projections of the special form qgq for an involution Hecke corner; this is an arbitrary finite-von-Neumann-algebra identity and applies to every unitary literal and every projection.
  finite-subgroup-hecke-literals-cannot-block-escape: that confines exact projection-valued literals supported on a finite subgroup; this needs no finite-support or group-algebra hypothesis and instead shows that a unitary-valued compression forces the corner to reduce the literal.
  non-ru-bcs-is-satisfiable-in-a-group-factor: that asks for the invariant group-factor corner which would solve the root goal; this proves that common-corner unitary dilation does not manufacture such a corner from weaker data.
---

**ESTABLISHED EXACT AND QUANTITATIVE COMPRESSION FENCE.**  Let `(M,tau)`
be a finite tracial von Neumann algebra, let `p` be a projection, and let
`u` be a unitary.  If `pup` is a unitary in the corner `pMp`, then

```text
up=pu,                                                       (UCR1)
```

so `pup=pu` is merely the restriction of `u` to a reducing corner.

More quantitatively, if `v` is a unitary in `pMp` and

```text
||pup-v||_2 <= epsilon,
```

then

```text
||(1-p)up||_2^2=||pu(1-p)||_2^2
   <= 2 sqrt(tau(p)) epsilon,
||[u,p]||_2 <= 2 tau(p)^(1/4) sqrt(epsilon).             (UCR2)
```

Consequently, in a tracial matrix ultraproduct, any literal group unitary
whose compression is unitary on `p` commutes with `p` exactly.  For a
family `u_i`, a common projection on which every `p u_i p` is unitary is a
common reducing projection.

Apply this to Boolean constraint variables.  If involutions `x_i` satisfying
a BCS are obtained as `x_i=p u_(g_i) p` from literal group unitaries in one
group factor, then `p` already belongs to the relative commutant of all
`u_(g_i)`, and the `x_i` already give the invariant-corner realization
asked for by `non-ru-bcs-is-satisfiable-in-a-group-factor`.  Independent
Julia/Halmos dilations, free Haar tags, or block swaps do not create that
realization: exact unitarity kills every off-corner dilation block, and
asymptotic unitarity kills it in normalized Hilbert--Schmidt norm by
`(UCR2)`.

This does not refute the group-factor endpoint.  It identifies the precise
missing input: the host group factor and its common reducing projection must
be constructed by genuinely non-Cartan multiplicative structure, rather
than obtained by dilating each already-unitary BCS variable.

DERIVATION
unitary-corner-reduction-proof
