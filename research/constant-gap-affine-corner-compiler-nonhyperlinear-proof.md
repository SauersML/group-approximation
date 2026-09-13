---
rg: 2
id: constant-gap-affine-corner-compiler-nonhyperlinear-proof
kind: route
title: Push the canonical corner trace through the affine decoder and hit the fixed AND-gadget value gap
target: constant-gap-affine-corner-compiler-forces-nonhyperlinear
requires:
  - affine-safe-value-of-magic-square-and-gadget-below-one
  - ce-exact-affine-compilers-force-nonhyperlinear-corners
  - thom-central-corner-criterion
artifacts:
  - research/artifacts/affine-support-value-gap-2026-09-13.md
---

Notation as in `constant-gap-affine-corner-compiler-forces-nonhyperlinear`.
Assume a constant-gap affine corner compiler for `B_tilde` with `s > 1 - c*`,
and suppose for contradiction that `Gamma` is hyperlinear.

## Step 1: the canonical trace is Connes-embeddable

`J` has order exactly `n` (it is the central character generator of a
nonzero corner). By Step 1 of `ce-exact-affine-compilers-nonhyperlinear-proof`,
the corner `(p_omega L(Gamma) p_omega, tau_omega)` is the twisted group von
Neumann algebra `L_(omega o alpha)[Gamma/<J>]`. By
`thom-central-corner-criterion` (Thom, Lemma 3.3), if `Gamma` is hyperlinear
then this algebra embeds trace-preservingly into `R^U`. So `tau_omega` is a
Connes-embeddable model of the corner.

## Step 2: apply the gap hypothesis

By `(GAP)`, the decoded strategy `S` from `tau_omega` is a synchronous
strategy for `B_tilde` with value `>= s`.

## Step 3: the decoded strategy is a canonical-corner pushforward

By construction `S` is obtained from the canonical trace `tau_omega` through
the affine decoder `D` of the form (GC5). This is exactly the object of part
`(VB)` of `affine-safe-value-of-magic-square-and-gadget-below-one`:
in each context the answer distribution is the pushforward under an affine map
of the uniform coset distribution `X_A(omega)` of (CS1), hence uniform on a
flat.

## Step 4: the value gap

Restrict `S` to the `B_MS^AND` component of `B_tilde`. It is still a
canonical-corner pushforward under `D`, so `(VB)` gives value `<= 1 - c*` on
that component. A disjoint-union game accepts only if the sampled component
accepts, so the value of `S` on `B_tilde` is at most the value on any
component, in particular `<= 1 - c*`.

## Step 5: contradiction

Steps 2 and 4 give `s <= value(S) <= 1 - c*`, contradicting `s > 1 - c*`.
Therefore `Gamma` is not hyperlinear.

## Note

Only the canonical trace is used, and only through (CS1) and Thom's criterion;
no perfect model of `B_tilde` is assumed, and no value gap on the target side
is needed. The whole argument is the exact-compiler proof of
`ce-exact-affine-compilers-nonhyperlinear-proof` with "perfect on CE models"
weakened to "value at least `s` on CE models" and the qualitative firewall
replaced by the quantitative `(VB)`.
