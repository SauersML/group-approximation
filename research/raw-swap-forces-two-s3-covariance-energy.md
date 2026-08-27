---
rg: 2
id: raw-swap-forces-two-s3-covariance-energy
kind: claim
title: The compiled raw swap forces positive energy in two fixed S3 covariance directions
distinct_from:
  full-raw-packet-commutant-witness: That extracts a coordinate-selected commutant unitary with large transported-carrier commutator; this is a fixed-word statement using only the two S3 letters that actually occur in the raw swap.
  pauli-carrier-membership-decoder: That asks for a positive membership/recovery statement for the transported Pauli carrier; this is the opposite quantitative lower bound forced by separation of the raw source word.
artifacts:
  - experiments/atlas-raw-compressor-source-words.json
  - experiments/atlas_raw_reynolds_gap_audit.py
  - notes/TRUE_RAW_WORD_REYNOLDS_GAP.md
---

Use the certified inner alignment of the two regular `A_8` charts in the
compiled atlas.  In the scalarized raw source word, all twelve syllables from
the second chart lie in one fixed subgroup

```text
H ~= S_3.
```

Moreover only two elements `a_0,b_0 in H` occur there, with multiplicities
`4` and `8`, and they are involutions whose product has order `3`, hence they
generate `H`.

Let `rho` denote the first-chart copy of the finite group and let `U` be the
relative chart unitary.  Put

```text
a = ||U rho(a_0) U^* - rho(a_0)||_2,
b = ||U rho(b_0) U^* - rho(b_0)||_2.
```

For every atlas microstate in which the raw source word has the regular-trace
separation required by the one-unitary criterion,

```text
a^2+b^2 >= 1/40-o(1).                                  (RSE)
```

More quantitatively, before taking the microstate limit,

```text
||raw(U)-1||_2 <= 4 a + 8 b + eta,
```

where `eta` is the total error from the finitely many already-fixed chart and
word identifications used in the certified alignment.  Thus whenever
`eta=o(1)` and `||raw(U)-1||_2 -> sqrt(2)`, `(RSE)` follows.

This is a finite fixed-library obstruction: no arbitrary element of a matrix
commutant is selected.  To contradict the raw source separation it is enough
to prove that the mixed Leavitt/atlas relations force these **two named**
covariance defects to tend to zero.
