---
rg: 2
id: deligne-triple-cover-is-not-mf
kind: claim
title: Deligne's triple cover of Sp4(Z) is not MF
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
  - research/artifacts/deligne-sector-tensor-camouflage-2026-08-21.md
distinct_from:
  deligne-central-mark-hs-collapse: that asks for normalized-Hilbert-Schmidt collapse and is equivalent to non-hyperlinearity of E_3; this asks only for failure of operator-norm MF approximation and is strictly the MF question.
  deligne-triple-cover-fd-central-invisibility: that concerns genuine finite-dimensional representations; this excludes faithful operator-norm asymptotic representations, which is the unproved upgrade.
---

For Deligne's central extension

```text
1 -> <z>=Z/3 -> E_3 -> Sp_4(Z) -> 1,
```

the group `E_3` is not MF in the norm-matrix-corona sense.

By `deligne-triple-cover-finite-residual-is-center` and
`universal-mf-quotient`, this is equivalent to each of

```text
z in Rad_MF(E_3),
Rad_MF(E_3) = <z> = C_3.                                (DMF1)
```

Indeed `Rad_MF(E_3) <= Res_fin(E_3)=C_3`, while a non-MF countable group has
nontrivial MF radical.  Since `C_3` has prime order, there is no intermediate
subgroup.

## Attempts

- **Exact representations stop one topology too early.**  Deligne plus
  Malcev proves that every genuine finite-dimensional representation kills
  `z`, but MF radical membership quantifies over operator-norm asymptotic
  representations.  `fd-mark-stability-forces-mf-invisibility` explains the
  missing stability hypothesis, and no such stability theorem is known here
  for `E_3`.
- **Do not substitute the HS endpoint.**  Universal normalized-HS collapse
  of `z` is `deligne-central-mark-hs-collapse`, which
  `deligne-sector-gap-is-exactly-nonhyperlinearity` identifies with the
  stronger open assertion that `E_3` is non-hyperlinear.  HS-small exceptional
  central sectors may still have operator norm one, so that claim cannot be
  silently used as an operator-norm proof.
- **Literature boundary.**  Bachner--Dogon--Lubotzky, *On L1-approximation of
  groups*, arXiv:2508.17392v3, Proposition 1.5, gives non-MF only under the
  additional operator--HS stability condition and explicitly presents it as
  a potential approach to the MF question.  No theorem in that source proves
  this fixed triple cover non-MF.
