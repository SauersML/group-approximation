---
rg: 2
id: kt-kazhdan-polar-compressor-rounding-is-directional
kind: claim
title: Kazhdan polar rounding of one compressor controls only the compressed stabilizer
distinct_from:
  kazhdan-polar-rounding-produces-supported-gallery-edges: That proves the general high-support partial-intertwiner theorem; this identifies its orientation in the Kun--Thom ascending HNN and proves why it cannot promote the forward lamp to the full Gamma commutant.
  kt-elementary-kazhdan-packet-rounds-base-lamp: That rounds a base lamp after the Gamma representation is exact; this shows that transporting the rounded lamp forward through a merely partial compressor intertwiner loses full Gamma invariance.
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: That proves full actor exactification fails using canonical one-compressor microstates; this isolates the exact support-extension step which fails even if the Gamma leg itself is exact.
---

**ESTABLISHED.**  Let `alpha:Gamma->Gamma` be a strict positive Kun--Thom
compressor and let `pi:Gamma->U(d)` be exact.  If a unitary `U` obeys

```text
eta=max_(s in K)||U pi(s) U^*-pi(alpha(s))||_2,         (KPD1)
```

then Kazhdan polar rounding gives an exact partial isometry `V` with

```text
pi(alpha(s))V=Vpi(s),
||U-V||_2<=2eta/kappa_K,
tr(1-V^*V)=tr(1-VV^*)<=eta^2/kappa_K^2.                (KPD2)
```

Put

```text
C=pi(Gamma)',                 D=pi(alpha(Gamma))'.
```

Then `C subset D`, `V^*V in C`, and `VV^* in D`.  For `P in C`, the forward
transport satisfies

```text
UPU^* =_O(eta/kappa_K) V P V^* in D,                  (KPD3)
```

but `VPV^*` need not belong to `C`.  Applying the same theorem to `U^*`
only puts the **backward** transport `U^*PU` near `C`.  Thus polar rounding
alone does not show that the lamp at the forward site `tGamma` is fixed by
all of `Gamma`; it recovers exactly its true stabilizer `alpha(Gamma)` and
nothing more.

The missing operation is extension of `V` to a full exact unitary
intertwiner.  Its source and range complements have `o(1)` physical trace,
but their representation types need not match.  Small support loss does not
control the dimension or inclusion index of the commutant, so it cannot imply
`C=D`.

This obstruction occurs in the actual one-compressor telescope, not just in
an abstract pair of representations.  Its finite coset models use exact
finite-quotient actions of `Gamma` on each telescope level and complete the
partial level shift to a permutation; `(KPD1)` tends to zero only through the
top and bottom boundary.  They retain the canonical separation between the
lamps at `tGamma` and `gamma tGamma` for
`gamma in Gamma\alpha(Gamma)`.  Therefore exactification of the Gamma leg
plus `(KPD2)` is not a terminal reduction.  One needs either a full-space
compressor intertwiner or a genuinely multi-compressor argument which charges
the unmatched support types.

DERIVATION
kt-kazhdan-polar-compressor-direction-proof
