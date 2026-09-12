---
rg: 2
id: extraspecial-common-gauge-fourier-controller-proof
kind: route
title: Diagonalize the unique spin packet and telescope the Pauli shifts
target: extraspecial-common-gauge-fourier-controller
requires:
  - gowers-hatami-finite-group-hs-stability
---

On the `J=-1` sector, Stone--von Neumann uniqueness identifies the Pauli
packet with `C^(2^k)` tensored with a multiplicity space.  Commutation with
the `Z_i` makes `C` coordinate diagonal.  Evaluating the relative
commutator in `(ESF2)` on coordinate `x` gives

```text
C_x C_(x+e_i)^(-1)=W_i,
```

and hence `C_x=W_x C_0`.  Compressing this diagonal matrix to the uniform
`X`-fixed vector gives the average in `(ESF5)`.  Fourier inversion for the
finite abelian payload group identifies that average with its trivial-type
projection.  The identity coefficient of `(ESF4)` is `1/(2|K|)`.

For approximate packets, finite-group HS rounding followed by the finite
conditional expectation onto the `Z` diagonal and a length-at-most-`k`
hypercube telescope gives a modulus depending only on the fixed packet.

Finally write the exact controller as `C=D_W A`, where
`D_W=sum_x |x><x| tensor W_x` and `A` acts only on the multiplicity space.
Choosing `S=A^*` makes `SC=A^*D_WA` an involution.  Since `S` commutes with
the whole spin packet, it commutes with the Reynolds atom `q`; hence
`qSCq=S qCq`.  This proves the gauge-absorbing statements `(ESF8)`--`(ESF9)`.
