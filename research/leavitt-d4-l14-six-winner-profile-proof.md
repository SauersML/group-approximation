---
rg: 2
id: leavitt-d4-l14-six-winner-profile-proof
kind: route
title: Classify and expose the two six-winner carrier systems
target: leavitt-d4-l14-six-winner-profile-has-two-classes
requires:
  - leavitt-d4-l14-first-profile-rank9-is-fenced
---

MSI job `16675107` gives exactly six balanced rank-nine winners for this
profile.  Cyclic quotienting gives normal `0;511` and inverse `1;412`, each
with multiplicity three.

For the normal class the exact carrier equations and boundary are

```text
H A0=E7^-1H,
H^-1C0=A1^-1H^-1,
H^-1C1=E5^-1H^-1E4^-1H E3^-1H^-1E2^-1H E1^-1H^-1,
K=H^-1B0 H^-1B1 H^-1E6.
```

For the inverse class they are

```text
H^-1B0=E1^-1H^-1E7^-1H,
H^-1C0=A1^-1H^-1,
H^-1B1=E6^-1H,
K=A0^-1H^-1C1^-1H E5^-1H^-1E4^-1H
  E3^-1H^-1E2^-1H.
```

Here `C0=g0_0` and `A1=g3_3`, so the common equation immediately forces
`g0=g3=1`.  These two systems are the complete nonabelian elimination target
for the profile.

