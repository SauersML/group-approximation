---
rg: 2
id: one-shift-folner-mass-is-depth-parity-balanced
kind: claim
title: One-shift Folner mass is automatically balanced between even and odd depths
distinct_from:
  fixed-shift-invariance-does-not-force-flat-profile: that shows translation invariance does not imply Haar flatness; this extracts the weaker parity conclusion that translation invariance does imply and that alternating p-three flux actually needs.
  lambda-exact-face-closes-at-p-three: that sought a full flat profile before applying flux; this removes that unnecessary intermediate target conditionally on authenticating the odd-band holonomy.
---

Let `mu` be a probability measure on `Z` (finite support is allowed) and let
`S mu(k)=mu(k-1)`.  With total variation normalized as
`TV=(1/2)||.||_1`, put

```text
m_even=sum_(k even)mu(k),       m_odd=sum_(k odd)mu(k).
```

Then

```text
|m_even-m_odd| <= TV(mu,S mu),                          (PBF1)
|m_odd-1/2| <= (1/2)TV(mu,S mu).                        (PBF2)
```

Consequently every sequence of depth profiles with one-step translation
defect tending to zero has asymptotic mass `1/2` on odd depth, even if it is
triangular, highly nonuniform, or stays far from Haar measure.

Suppose additionally that a decoded p-three loop has phase `-1` on every
odd-depth good band.  If `E_odd` is the good odd-band projection, the two
route operators `R_1,R_2` are isometries on it, the presentation relation
gives

```text
||(R_1-R_2)E_odd||_2 <= epsilon,
```

and authenticated holonomy gives

```text
||(R_1+R_2)E_odd||_2 <= eta,
```

then

```text
tau(E_odd) <= (epsilon+eta)^2/4.                        (PBF3)
```

Thus, once exceptional-band mass is negligible and the multiplicity gauge
is authenticated, shift invariance contradicts the alternating holonomy
without any flat-to-Haar theorem.  The remaining issue is precisely the
multiplicity authentication fenced by
`p3-minus-flux-is-cancelled-by-pauli-multiplicity`.
