---
rg: 2
id: deligne-universal-cover-lattice-is-not-hyperlinear
kind: claim
title: Deligne's universal-cover lattice over Sp4(Z) is not hyperlinear
distinct_from:
  dogon-sp2g-weak-ucp-nonhyperlinear: that proves this statement under weak ucp-stability of Sp_2g(Z); this is the unconditional statement at genus two.
  deligne-universal-cover-lattice-is-not-mf: that is the operator-norm statement about the same lattice; this is the tracial one. Neither is known to imply the other, but both imply finiteness of P_op, and under (CPE*) this one implies that one.
  deligne-stable-triple-cover-is-not-hyperlinear: that asks for non-hyperlinearity of the triple cover E_3, which is 1/3 notin E_CE; this asks only that E_CE be finite, with no control of its order, so it is implied by the genus-two case of that claim and is not known to imply it.
  maslov-ce-subgroup-classifies-finite-deligne-covers: that classifies the finite covers; this is equivalent to some finite cover being non-hyperlinear, without naming which.
---

**OPEN.** Let `Gamma~ = E_infinity` be the preimage of `Sp_4(Z)` in the universal cover of `Sp_4(R)`. The claim is
that `Gamma~` does not embed in the unitary group of a matricial tracial ultraproduct.

**Equivalent forms** (`deligne-norm-parameter-group-embeds-in-ce-subgroup`, (NCE3)):
- `E_CE` is finite;
- some finite Deligne cover `E_q` of `Sp_4(Z)` is not hyperlinear (for instance every prime `q` not dividing
  `|E_CE|`).

**Why it matters.**
- By (NCE3), it makes `P_op` finite. With `deligne-finite-parameter-group-has-period-prime-to-three`, it gives the
  flagship `deligne-triple-cover-exact-mf-radical`, through route
  `deligne-triple-cover-via-lattice-non-hyperlinear`.
- `Gamma~` is finitely presented, being a central extension of the finitely presented `Sp_4(Z)` by `Z`. So this
  claim also answers `non-hyperlinear-group`.
- It is implied by weak ucp-stability, equivalently flexible HS-stability, of `Sp_4(Z)`
  (`dogon-sp2g-weak-ucp-nonhyperlinear`). It is also implied by the LLP of `C^*(Sp_4(Z))`, through
  `sp4-llp-failure-or-maslov-nonhyperlinear-extension` together with (NCE3).

**How it can fail.** It fails exactly when `E_CE = R/Z`, that is, when every twisted factor `L_(c_theta)(Sp_4(Z))` is
Connes embeddable. That alternative forces `C^*(Sp_4(Z))` to fail LLP
(`sp4-llp-failure-or-maslov-nonhyperlinear-extension`). A single irrational CE parameter already suffices, by
closedness.

**What does not transfer.** Non-hyperlinearity is tracial. So by `deligne-lattice-norm-models-are-tracially-blind`
it cannot by itself say which central powers an operator-norm model kills. Its norm consequence is finiteness of
`P_op`, and no more without `(CPE*)`.
