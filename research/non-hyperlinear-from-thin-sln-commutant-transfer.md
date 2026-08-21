---
rg: 2
id: non-hyperlinear-from-thin-sln-commutant-transfer
kind: route
title: The thin-subgroup commutant modulus makes an explicit SL_n(Z) HNN extension non-hyperlinear
target: non-hyperlinear-group
requires:
  - sln-z-thin-codense-tau-pair
  - thin-sln-robust-relative-commutant-transfer
---

Let `A = SL_n(Z)`, let `C = <c_1,c_2,c_3,c_4>` be the thin profinitely
dense subgroup of `sln-z-thin-codense-tau-pair`, choose `a in A \ C`, and
form

```text
G = <A,t | [t,c_i]=1, 1 <= i <= 4>.                    (NHT1)
```

This is finitely presented.  Britton's lemma gives `[t,a] != 1` in `G`.

Assume `G` were hyperlinear and take canonical-trace matrix microstates.
Restricting them to `A` gives approximate representations of the fixed
presentation of `A`; let `v` be the matrix assigned to `t`.  The HNN
relators give

```text
max_i ||[v,c_i(U)]-1||_2 -> 0.                         (NHT2)
```

By `thin-sln-robust-relative-commutant-transfer`,

```text
||[v,a(U)]-1||_2 -> 0.                                 (NHT3)
```

But `[t,a]` is a nonidentity group element, so canonical-trace microstates
must have `tr([v,a(U)]) -> 0`, equivalently
`||[v,a(U)]-1||_2 -> sqrt(2)`.  This contradicts `(NHT3)`.

Thus `(NHT1)` is non-hyperlinear once the one-unitary transfer modulus is
proved.  This route is strictly more targeted than
`non-hyperlinear-from-hnn-over-sln-z`: it does not require correcting the
whole approximate `SL_n(Z)` tuple to an exact representation.
