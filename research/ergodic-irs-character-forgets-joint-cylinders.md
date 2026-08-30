---
rg: 2
id: ergodic-irs-character-forgets-joint-cylinders
kind: claim
title: Even among ergodic IRSs the complete character forgets joint membership cylinders
distinct_from:
  irs-character-does-not-determine-haar-cylinders: that uses two nonergodic mixtures on S3; this gives two finite-orbit ergodic IRSs with the same complete character and different two-word cylinders.
  ergodic-irs-factor-components-need-not-be-stabilizer-characters: that concerns factor summands leaving the IRS-character image; this shows information loss already inside the class of ergodic IRSs.
  manzoor-separation-does-not-specify-haar-cylinders: that audits the unspecified Manzoor witness; this is a fully explicit Gassmann collision independent of that construction.
---

There are two ergodic IRSs `theta_1,theta_2` of `S_6` such that

```text
theta_1({K:g in K})=theta_2({K:g in K})  for every g,   (EGC1)
```

but for explicit `a,b in S_6`,

```text
theta_1({K:a,b in K})=1/15,
theta_2({K:a,b in K})=0.                               (EGC2)
```

Take the uniform measures on the conjugacy orbits of the two nonconjugate
almost-conjugate Klein four subgroups

```text
H_1={1,(12)(34),(13)(24),(14)(23)},
H_2={1,(12)(34),(12)(56),(34)(56)}.                    (EGC3)
```

Each measure is the stabilizer distribution of a finite transitive pmp
action and hence is ergodic. Thus passing first to an ergodic IRS does not
make the stabilizer character determine its subgroup law. In particular no
central decomposition performed only on the GNS character can reconstruct
the joint readable cylinders needed by a measure-level argument.
