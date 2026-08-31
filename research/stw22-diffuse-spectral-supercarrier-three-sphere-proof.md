---
rg: 2
id: stw22-diffuse-spectral-supercarrier-three-sphere-proof
kind: route
title: Bootstrap the spectral supercarrier through projection and stabilizer degree two
target: stw22-diffuse-stiefel-uniform-three-sphere-fillings
requires:
  - stw22-diffuse-stiefel-uniform-two-sphere-fillings
  - stw22-diffuse-spectral-supercarrier-two-sphere-proof
artifacts:
  - research/artifacts/stw22-diffuse-three-sphere-supercarrier-audit-2026-08-31.md
---

All metrics are ambient `2`-metrics.

## 1. Fixed-trace Grassmannians are uniformly two-connected

For a diffuse corner `fNf`, fix a projection `r<=f`. The orbit map

```text
pi:U(fNf)->{p<=f:tau(p)=tau(r)},       pi(u)=uru^*     (G3-1)
```

has fibres isometric to

```text
U(rNr) times U((f-r)N(f-r)).                           (G3-2)
```

Zero corners are interpreted as singletons. The degree-zero and degree-one Stiefel theorems make (G3-2) simply
connected with common `LC^0` and `LC^1` moduli. The close-
projection unitary lemma inside `fNf` makes the inverse multifunction
lower semicontinuous and gives pointwise conjugators close to the identity.

For a sufficiently small projection sphere `p:S^2->Proj_tau(r)(fNf)`,
Gutev's controlled Michael theorem with `n=1` therefore selects a small
unitary sphere `u:S^2->U(fNf)` with `p=uru^*`. The universal degree-two unitary Stiefel modulus then fills `u`; conjugating `r` by that fill gives a
small filling of `p`. For an arbitrary projection sphere, the uncontrolled
Michael theorem with `n=1` selects a lift, and Jekel contracts it. Hence
fixed-trace projection Grassmannians are two-connected and form a uniform
equi-`LC^2` family. Normalized-corner scaling plus the small-corner diameter
split makes this control independent of all corner and projection traces.

The same conclusion holds for

```text
P(h,q;s)={p:h<=p<=q, tau(p)=s},                         (G3-3)
```

after translation by `h`, whenever `tau(h)<=s/2` and `s<tau(q)`: its ambient
corner `q-h` has trace greater than `tau(q)/2`.

## 2. Select a supercarrier over S^3

For `x:S^3->Nq`, put

```text
a_z=|x(z)|,       h_z=1_[kappa,infinity)(a_z),
s=2delta^2/kappa^2.                                    (G3-4)
```

If `delta=0`, take `e_z=0`. If `s>=tau(q)`, take `e_z=q`. Otherwise use
the multifunction `Phi(z)=P(h_z,q;s)`. Its lower semicontinuity is
dimension-free and was proved in the required two-sphere route: the
inclusive cutoff controls atoms at `kappa`, the Hilbert--Schmidt Sylvester
estimate controls spectral crossing, and the polar-range correction uses
a close-projection unitary inside `qNq`.

By Step 1 the values are closed, two-connected, and equi-`LC^2`.
Michael's theorem with `n=2` over `S^3` selects `e_z`. Functional calculus
gives `||x(z)(q-e_z)||<=kappa`, proving (SC3).

## 3. Localize and lift the pair

For a small frame sphere, normalize its centre to `q` and apply (SC3) to
`x=v-q`. The same dimension-free direct rotation gives a homotopy, within
`delta+10kappa` of `q`, to

```text
v'(z)=q-e_z+w_z,
w_z^*w_z=e_z,       w_zw_z^* orthogonal to q-e_z.      (G3-5)
```

Fix a base pair `(e_*,w_*)`. The carrier conjugator values

```text
{a in U(qNq):ae_*a^*=e_z}                              (G3-6)
```

and the corresponding partial-isometry conjugator values in
`(1-q+e_*)N(1-q+e_*)` have stabilizers which are products of diffuse
corner unitary groups or singletons. The new degree-two Stiefel theorem
makes those stabilizers two-connected and equi-`LC^2`. Their inverse
multifunctions are lower semicontinuous by the close-projection and
close-frame lemmas. Michael with `n=2` therefore selects unitary
three-spheres `a_z,c_z` satisfying

```text
e_z=a_ze_*a_z^*,       w_z=a_zc_zw_*a_z^*.             (G3-7)
```

Jekel-contract `a` and `c` to their corner identities and substitute the
contractions in (G3-7). Throughout, the represented frame differs from
`q` on a right carrier of trace `tau(e_*)`, so the fill radius is at most

```text
2sqrt(tau(e_*))<=2sqrt(2)delta/kappa.                  (G3-8)
```

With `epsilon_0=min(epsilon,1)`, `kappa=epsilon_0/40`, and
`delta=epsilon_0^2/1000000`, both the direct-rotation collar and (G3-8)
lie inside the `epsilon`-ball. This proves (DS3).

For an arbitrary `S^3->St_N(q)`, apply Michael with `n=2` to the
unitary-conjugator multifunction carrying one base frame to the sphere.
Its stabilizer is a diffuse corner unitary group or a singleton, hence is
two-connected and equi-`LC^2`. Jekel contracts the selected unitary
sphere, proving global three-connectivity.

Primary inputs are E. Michael, *Continuous Selections II*, Theorem 1.2;
V. Gutev, *Constructing selections stepwise over skeletons of nerves of
covers*, Theorem 5.3; I. Farah and A. Vaccaro, *Continuous Selection of
Unitaries in II1 Factors*, Theorem 1.1 and Claims 3.1--3.2; D. Jekel,
*The unitary group of a II1 factor is SOT-contractible*, Theorem A; and
M. Takesaki, *Theory of Operator Algebras III*, Lemmas XIV.2.1--2.