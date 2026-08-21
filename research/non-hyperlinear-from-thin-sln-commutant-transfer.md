---
rg: 2
id: non-hyperlinear-from-thin-sln-commutant-transfer
kind: route
title: The thin-subgroup commutant modulus makes an explicit finitely presented SL_3(Z) HNN extension non-hyperlinear
target: non-hyperlinear-group
requires:
  - explicit-sl3-thin-codense-tau-pair
  - thin-sln-robust-relative-commutant-transfer
---

Let `A = SL_3(Z)` and let `a,b,r` be the displayed matrices of
`explicit-sl3-thin-codense-tau-pair`.  Thus `C=<a,b>` is free and
profinitely dense, while `r` has order three and hence `r notin C`.  Form

```text
G = <A,t | [t,a]=1, [t,b]=1>.                          (NHT1)
```

This is a literal finite presentation.  Britton's lemma gives
`[t,r] != 1` in `G`.

Assume `G` were hyperlinear and take canonical-trace matrix microstates.
Restricting them to `A` gives approximate representations of the fixed
presentation of `A`; let `v` be the matrix assigned to `t`.  The HNN
relators give

```text
max(||[v,a(U)]-1||_2, ||[v,b(U)]-1||_2) -> 0.          (NHT2)
```

By `thin-sln-robust-relative-commutant-transfer`,

```text
||[v,r(U)]-1||_2 -> 0.                                 (NHT3)
```

But `[t,r]` is a nonidentity group element, so canonical-trace microstates
must have `tr([v,a(U)]) -> 0`, equivalently
`||[v,a(U)]-1||_2 -> sqrt(2)`.  This contradicts `(NHT3)`.

Thus `(NHT1)` is non-hyperlinear once the one-unitary transfer modulus is
proved.  This route is strictly more targeted than
`non-hyperlinear-from-hnn-over-sln-z`: it does not require correcting the
whole approximate `SL_n(Z)` tuple to an exact representation.
