---
rg: 2
id: v-binary-shell-envelope-is-finitely-presented
kind: claim
title: The genuine-action shell envelope of Thompson's V with its binary action on N is finitely presented
distinct_from:
  thompson-v-binary-shell-action-passes-both-germ-gates: that proves the germ group finitely presented; this asks for the envelope itself, the first test of whether passing the germ gates suffices.
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that proves envelopes finitely presented through a central shift power; this test case has no central shift power, since V is not virtually abelian.
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**OPEN.** Let `rho` be the binary action of `V` on `N` from `thompson-v-binary-shell-action-passes-both-germ-gates`.
Then `E_rho = <V, hat(rho(V))>` is finitely presented.

**Why it matters.** It is the first case where both germ gates pass for an input that is not virtually
abelian. So it tests the converse of `shell-envelope-fp-forces-fp-germ-group`, which is what the universal
route needs. The input itself carries no Boone–Higman content.

**Known.**
- Necessary conditions: they all hold (germ group and fiber product finitely presented).
- Belk–Hyde–Matucci Theorem 2.1 reduces the claim to finite presentation of `S(M,M')`, `|M'| <= 2`. The
  first case is `A_1`, the extension of `Q_rho` by the neighbourhood kernel `K`, an ascending union of
  copies of `V`.
- The lift `hat(rho(V))` together with the prefix germ lift `0y -> 00y, 10y -> 1y, 11y -> 01y` gives a
  candidate section of `A_1 -> Q_rho`. Whether it is a section (injective on the relations of `Q_rho`) is
  the first thing to check.
