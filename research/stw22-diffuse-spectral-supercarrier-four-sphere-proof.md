---
rg: 2
id: stw22-diffuse-spectral-supercarrier-four-sphere-proof
kind: route
title: Bootstrap the spectral supercarrier through degree-three Grassmannian and stabilizer control
target: stw22-diffuse-stiefel-uniform-four-sphere-fillings
requires:
  - stw22-diffuse-stiefel-uniform-three-sphere-fillings
artifacts:
  - research/artifacts/stw22-diffuse-four-sphere-supercarrier-audit-2026-08-31.md
---

All metrics are ambient `2`-metrics.

## 1. Projection Grassmannians reach degree three

For the orbit map

```text
U(fNf)->{p<=f:tau(p)=t},       u |-> uru^*,            (G4-1)
```

the fibres are products of corner unitary groups. The degree-two Stiefel
theorem makes them two-connected with common local moduli through degree
two. The close-projection lemma gives lower semicontinuity and conjugators
close to the identity.

Controlled Michael selection with `n=2` therefore lifts a small projection
`S^3` to a small unitary `S^3`. Fill that lift by the universal degree-
three unitary Stiefel modulus and conjugate `r`. The uncontrolled selection
followed by Jekel contraction treats arbitrary projection `S^3` maps.
Hence fixed-trace projection Grassmannians are three-connected and
uniformly equi-`LC^3`. Normalized-corner scaling and the small-corner
diameter split make the moduli independent of all traces.

The translated values

```text
P(h,q;s)={p:h<=p<=q, tau(p)=s}                         (G4-2)
```

inherit this conclusion whenever `tau(h)<=s/2` and `s<tau(q)`.

## 2. Select the S^4 supercarrier

For `x:S^4->Nq`, put

```text
a_z=|x(z)|,       h_z=1_[kappa,infinity)(a_z),
s=2delta^2/kappa^2.                                    (G4-3)
```

The cases `delta=0` and `s>=tau(q)` use `e=0` and `e=q`, respectively.
In the remaining case, the inclusive spectral-superprojection
multifunction `P(h_z,q;s)` is lower semicontinuous by the dimension-free
Sylvester/polar-range proof. Its values are closed, three-connected, and
equi-`LC^3` by Step 1. Michael with `n=3` over `S^4` selects `e_z` and
functional calculus gives (SC4).

## 3. Localize and lift over S^4

Apply (SC4) to `x=v-q` after normalizing the centre of a small frame
sphere. The dimension-free direct rotation homotopes it, within
`delta+10kappa` of `q`, to

```text
q-e_z+w_z,       w_z^*w_z=e_z,
w_zw_z^* orthogonal to q-e_z.                          (G4-4)
```

The carrier and partial-isometry conjugator multifunctions have stabilizers
which are products of diffuse corner unitary groups or singletons. The
degree-three Stiefel theorem makes them three-connected and equi-`LC^3`.
Michael with `n=3` selects both unitary `S^4` lifts. Contract them by Jekel
and substitute the contractions in (G4-4). Every represented frame remains
supported on a right carrier of trace `tau(e_z)`, so the fill radius is at
most

```text
2sqrt(2)delta/kappa.                                   (G4-5)
```

Take `epsilon_0=min(epsilon,1)`, `kappa=epsilon_0/40`, and
`delta=epsilon_0^2/1000000`. The direct-rotation collar and (G4-5) lie
inside the requested ball, proving (DS4).

For an arbitrary frame `S^4`, Michael with `n=3` selects a unitary sphere
carrying one base frame to it; the stabilizer has the same degree-three
properties. Jekel contracts the lift, proving global four-connectivity.