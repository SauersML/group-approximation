---
rg: 2
id: sl3-primary-mass-has-a-uniform-quadratic-gap
kind: claim
title: Denominator-primary congruence mass is bounded by squared intertwining defect independently of conductor
distinct_from:
  sl3-primary-exact-congruence-mass-vanishes-at-every-prime: that proves qualitative primary-mass vanishing as the overlap defect tends to zero; this supplies a uniform quadratic bound by amplification and is the rate needed for linear packet repair.
  lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible: that bounds primary mass by conductor depth times squared defect; this removes the depth factor, including at prime two and for arbitrary multiplicities.
  fixed-projective-gap-forces-primary-congruence-mass: that lower-bounds primary mass in a surviving projective witness; this upper-bounds the same mass by the fixed overlap defect and consequently excludes such a witness after exact lattice correction.
  exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss: that treats representations concentrated in one exact conductor band; this permits arbitrary mixtures across all conductor depths.
artifacts:
  - research/artifacts/independent-kirillov-primary-sector-audit-2026-09-08.md
  - research/artifacts/sl3-primary-mass-quadratic-amplification-2026-09-08.md
---

Fix a prime `p`, put `C=SL_3(Z)`, `h=diag(p,1,p^(-1))`, and
`D=C intersection h^(-1) C h`, and fix a finite Kazhdan generating
set `S_D` for `D`. There is a constant `K_p<infinity` with the
following property.

Let `sigma:C->U(d)` factor through `SL_3(Z/(p^a m))`, where
`gcd(p,m)=1`, and let `H` be any unitary. Let `P` project onto the
subspace on which the entire `p`-primary factor acts trivially and set

```text
q=1-tr_d(P),
epsilon=max_(s in S_D) ||H sigma(s)-sigma(hsh^(-1)) H||_2.
```

Then

```text
q <= K_p epsilon^2.                                    (PQG)
```

The norms and trace are normalized by `d`. The constant depends on the
fixed prime and generating set, but not on dimension, conductor, coprime
level, irreducible type, or multiplicities. It is proved to exist; no
numerical value or effective algorithm for finding it is asserted.

More generally the same inequality holds in every finite von Neumann
algebra with a normalized faithful tracial state, replacing `tr_d` by
that trace and taking `P` to be the finite-group average of the primary
factor. The constant is also independent of the coordinate algebra.

The result concerns genuine congruence representations of `C`. It does
not replace that hypothesis by arbitrary unitary microstates. Property
T is used explicitly in its proof.
