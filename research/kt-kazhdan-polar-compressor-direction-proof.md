---
rg: 2
id: kt-kazhdan-polar-compressor-direction-proof
kind: route
title: Orient the partial intertwiner along the ascending HNN edge
target: kt-kazhdan-polar-compressor-rounding-is-directional
requires:
  - kazhdan-polar-rounding-produces-supported-gallery-edges
  - kt-elementary-kazhdan-packet-rounds-base-lamp
  - kun-thom-single-compressor-sofic-joint-nonsofic
  - kt-single-compressor-canonical-lamps-do-not-exactify-actor
---

Apply `kazhdan-polar-rounding-produces-supported-gallery-edges` to
`pi_-=pi`, `pi_+=pi after alpha`, and `A=U`.  This is exactly `(KPD2)`.
The support identities follow by taking adjoints in the intertwining
equation.  Since `alpha(Gamma) subset Gamma`, commutants reverse to give
`C subset D`.

For `P in C`, it also commutes with `pi(alpha(Gamma))`; hence `VPV^*`
commutes with `pi(alpha(Gamma))` and belongs to `D`.  The two-unitary
telescoping estimate gives

```text
||UPU^*-VPV^*||_2<=2||U-V||_2<=4eta/kappa_K.
```

There is no corresponding calculation placing `VPV^*` in `C`: the
intertwining equation has target representation `pi after alpha`.  Reversing
the edge reverses which lamp is controlled, rather than changing `D` into
`C`.

The one-compressor soficity proof uses the standard ascending-HNN telescope.
On a finite stack, the horizontal `Gamma` action is a direct sum of genuine
finite quotient permutation representations.  The compressor is the level
shift on the interior and is completed on the two boundary levels.  Boundary
proportion tends to zero, proving `(KPD1)`, while the forward coset has
stabilizer `alpha(Gamma)` and its distinct translates retain their regular
lamp trace.  This is precisely a sequence of high-support partial
intertwiners whose complements cannot be representation-theoretically
matched.  It proves the asserted firewall.
