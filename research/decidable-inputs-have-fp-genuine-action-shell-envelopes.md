---
rg: 2
id: decidable-inputs-have-fp-genuine-action-shell-envelopes
kind: claim
title: Every decidable finitely generated group lies in an input with a genuine infinite-support action whose shell envelope is finitely presented
distinct_from:
  decidable-inputs-have-fp-shell-envelopes: that asks for a regular enumeration of the given input; this allows any genuine action of any overgroup with infinite supports, so it is implied by that claim and is a priori weaker.
  perfect-decidable-inputs-have-fp-shell-envelopes: that restricts to perfect inputs and regular enumerations; this allows arbitrary actions and makes no perfectness assumption, since simplicity comes from the twisted Brin–Thompson step.
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**OPEN.** For every finitely generated group `G` with decidable word problem there are an
infinite finitely generated group `P >= G` and an action `rho: P -> Sym(N)` in which every
nonidentity element has infinite support, such that the shell envelope `E_rho` of
`genuine-action-shell-envelopes-generalize-the-regular-shell` is finitely presented.

It implies `boone-higman-conjecture` by route
`boone-higman-via-genuine-action-shell-envelopes`. It is implied by
`decidable-inputs-have-fp-shell-envelopes` (take `P = P_0 × Z` from Clapham and the regular
action), so it is no harder than that claim.

## Known

- **Virtually abelian `P`:** holds, by eventually periodic actions
  (`eventually-periodic-genuine-shell-actions-give-fp-envelopes`). This includes one-ended
  inputs such as `Z^2`, which no regular enumeration has been shown to handle.
- **Necessary conditions that still bind** (item 3 of the generalization claim): `Q_rho`, hence
  `R_rho = <rho(P), s>`, must be finitely presented, and `R_rho` must pass the ascending HNN
  gate. The regular-only obstructions (one-ended window `N >= 1`, the virtually cyclic
  prefix-core cap) do not bind.
- **Ceiling of the normal-core method:** a central `<tau^k>` in `Q_rho` forces `P` virtually abelian.
  Twisted self-normalization `s^-1 rho(P) s = rho(P)` near infinity with a finite-order twist
  forces the same. So any input that is not virtually abelian needs `R_rho` to be finitely
  presented by a different mechanism, and either a twist of infinite order or a window `N >= 1`.

## Attempts

1. (bh-shell-universal, 09-18) Generalized the shell to genuine actions and found the
   virtually abelian positive family, including one-ended `Z^k`. No mechanism beyond
   eventual periodicity was found; the step past virtually abelian inputs is the whole content.
2. (bh-shell-universal, 09-18) Both germ gates pass for an input that is not virtually abelian:
   `thompson-v-binary-shell-action-passes-both-germ-gates` (V with its binary action; near group the
   odometer Röver–Nekrashevych group). So the gates are not the obstruction. What remains:
   - (a) finite presentation of an envelope whose germ group is finitely presented but has no central
     shift power; the first test is `v-binary-shell-envelope-is-finitely-presented`;
   - (b) near groups outside `B`, since inputs in `B` already embed in finitely presented simple groups.
   `shell-envelopes-depend-only-on-the-near-image` reduces (b) to: embed `G` in a finitely presented
   `R <= NearSym(N)` containing `s`, with `±chi` in `Sigma^1(R)`. `shell-shift-admits-no-baumslag-solitar-conjugation`
   excludes cyclic ascending bases.
