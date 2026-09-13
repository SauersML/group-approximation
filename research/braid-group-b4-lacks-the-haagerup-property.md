---
rg: 2
id: braid-group-b4-lacks-the-haagerup-property
kind: claim
title: The braid group B_4 does not have the Haagerup property
distinct_from:
  braid-group-b4-has-the-haagerup-property: that claim is the negation of this one
  some-braid-group-lacks-the-haagerup-property: that claim is failure for some n; this is failure at n = 4, which implies it
---

`B_4` admits no proper conditionally negative definite function. By
`braid-haagerup-induction-reduces-to-brunnian-braids`, this is equivalent to: every cnd function on `P_4`
fails to be proper on the free normal subgroup `Brun_4` of Brunnian braids.

## Attempts

- **Standard obstructions are absent.** There are no Kazhdan subgroups
  (`braid-groups-have-no-nontrivial-kazhdan-subgroups`) and no Burger pairs
  (`braid-abelian-normalizer-actions-are-virtually-solvable`).
- **Relative (T) along `F_2` or `F_3` fails.** `(B_4/Z(B_4), F_2)` and `(P_4, ker d_4)` do not have relative
  (T): tree functions pulled back along strand-deleting maps are unbounded on them. A relative (T) set must
  escape within finitely many `Brun_4`-cosets (§1 and §6 of
  `research/artifacts/zp-braid-haagerup-b4-attacks-2026-09-13-part3.md`).
- **Lifting Burger's argument.** The quotient `(B_4/Z)/[F_2, F_2]` is `Z^2`-by-`SL_2(Z)` with relative (T), but
  relative (T) does not lift from quotients. Burger's spectral argument needs an abelian normal subgroup and has
  no analogue for `F_2` or `Brun_4`. Open: a representation-theoretic obstruction on `Brun_4`, for example
  through the action of `P_4` on the space of cnd functions of `Brun_4`.
