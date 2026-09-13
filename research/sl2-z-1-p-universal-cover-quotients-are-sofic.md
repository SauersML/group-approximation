---
rg: 2
id: sl2-z-1-p-universal-cover-quotients-are-sofic
kind: claim
title: Every finite quotient of the universal-cover central extension of SL_2(Z[1/p]) by its central Z is sofic
distinct_from:
  sl2-half-central-extension-not-residually-amenable: that says these extensions are not residually amenable, so soficity is not automatic; this asks for soficity itself.
  dv-s-arithmetic-hs-stable-nonhyperlinear-extension: that turns Hilbert--Schmidt stability of the base into a non-hyperlinear extension of this kind; this is the opposite outcome, and it would make the base not Hilbert--Schmidt stable.
---

**OPEN.** Let `p` be prime and `Q = SL_2(Z[1/p])`, a lattice in `SL_2(R) × SL_2(Q_p)`. Let `Γ~` be its preimage in
`SL_2(R)~ × SL_2(Q_p)`, a central extension of `Q` by `Z`, and put `W_m = Γ~ / mZ`. The claim is that `W_m` is sofic
for every `m >= 1`.

**Routes in.** `sl2-z-1-p-cover-quotients-sofic-from-weak-lifts` derives it from
`deligne-sl2-z-1-p-weakly-bernoulli-lift`, through `weakly-bernoulli-liftable-action-makes-extension-sofic`.

**Consequences.**
- Every `W_m` would be hyperlinear. Dogon--Vigdorovich's non-hyperlinear extension of a Hilbert--Schmidt stable
  `S`-arithmetic lattice is a quotient `Γ~/NZ` of this kind (`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`).
- So `SL_2(Z[1/p])` would not be Hilbert--Schmidt stable. Their route to `non-hyperlinear-group` through
  `iwahori-local-global-defect-question` would close for these bases.
- Conversely, a non-hyperlinear `W_m` refutes this claim and, through the route above, refutes
  `deligne-sl2-z-1-p-weakly-bernoulli-lift`.

**Status.** Some `W_m` are not residually finite (Deligne--Raghunathan, recorded in
`sl2-half-central-extension-not-residually-amenable`). By Margulis they are not residually amenable. No soficity
result for them was found, but the check was bounded: a Cairn search only, with no literature search.
