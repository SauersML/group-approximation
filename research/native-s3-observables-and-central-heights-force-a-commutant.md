---
rg: 2
id: native-s3-observables-and-central-heights-force-a-commutant
kind: route
title: Capture two native S3 generators and use central heights to commute with all of H
target: native-s3-algebra-enlargement-obstructs-scalar-commutants
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/leavitt-native-s3-algebra-enlargement-obstruction-2026-09-08.md
---

The two native fourth-coordinate units are the opposite constant
transvections on the prefix leaves `000,1`, and hence generate `S_3`.
Conjugation by the fixed compressor gives `x_14(a),x_41(b)`.
Their commutators with `x_21(rb),x_12(ar)` give every coefficient
in roots `24,42`; the other roots follow inside `L`. This proves
the required finite-observable generation of `H`.

Haar averaging converts the assumed generator energies into uniform
`L`-centralization of the supplied algebra. The image `x_14(a)`
has an explicit infinite conjugacy orbit under `L`, so canonical trace
averaging makes its expectation onto that algebra tend to zero.
Capturing `k_+` puts this same image near the conjugate algebra,
forcing reverse leakage to tend to one.

The finite central-overlap flow then gives a trace-zero central height
of fixed positive variance which asymptotically commutes with the
compressor. It already nearly commutes with `L`; centrality and
capture of `k_+,k_-` give the remaining two commutators. Native
generation puts its limit in the full `H`-commutant.

The artifact reproduces the height lemma and its constants, includes
a one-word positive reverse bound, and explains why the exactified
finite `S_3` algebra has insufficient forward inclusion. It does not
assume that a finite observable set supplies the required enlargement.
