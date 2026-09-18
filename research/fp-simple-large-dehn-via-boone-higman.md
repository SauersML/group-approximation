---
rg: 2
id: fp-simple-large-dehn-via-boone-higman
kind: route
title: Embed the dual-certificate group of an almost-everywhere hard set into a finitely presented simple group
target: fp-simple-dehn-functions-realize-every-recursive-lower-bound
requires:
  - boone-higman-conjecture
  - dual-certificate-groups-force-large-host-dehn-functions
---

Fix total recursive `f`.

- `dual-certificate-groups-force-large-host-dehn-functions` gives a finitely
  generated group `H_f` with solvable word problem, such that every finitely
  presented group containing `H_f` has `f(n) <= K delta(Kn) + Kn` for all `n >= 1`.
- `boone-higman-conjecture` embeds `H_f` in a finitely presented simple group `S`.
- So `f ≼ delta_S`.

The inequality holds for `n >= 1`. At `n = 0` it reads `f(0) <= 0`, which no
Dehn function can meet for `f(0) > 0`, so the target's "for all `n`" can only
mean `n >= 1`.

**Contrapositive.** A proof of `a-recursive-function-is-no-fp-simple-dehn-lower-bound`
would refute the Boone–Higman conjecture. So the by-no answer to Zaremsky 1.16
under the strong reading is at least as hard as disproving Boone–Higman.

**Remaining input.** Only the Boone–Higman embedding. A weaker input suffices:
embed the specific groups `G_A * G_(N \ A)`, for recursive `A`, into finitely
presented simple groups. These are free products of HNN extensions of `F_2` along
recursively generated free factors of an infinitely generated free subgroup.
