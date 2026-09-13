---
rg: 2
id: zaremsky-1-10-fp-infinite-simple-amenable-group
kind: claim
title: "Zaremsky Problem 1.10 resolved: is there a finitely presented (or F_infinity) infinite simple amenable group?"
root: true
distinct_from:
  fp-infinite-simple-amenable-group: that is the existence statement, one of the two answers; this is the question as printed, established by that existence claim or by its negation no-fp-infinite-simple-group-is-amenable
  hyperlinear-fp-infinite-simple-group: that asks for a finitely presented infinite simple hyperlinear group, which an amenable example would supply; this is the amenable question as printed by Zaremsky
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 10, verbatim:
"Find a finitely presented (or F∞), infinite, simple, amenable group."

This claim is the question. It is established only through an answer route:
- **Construction**: `zaremsky-1-10-by-construction` requires `fp-infinite-simple-amenable-group`.
- **Nonexistence**: `zaremsky-1-10-by-nonexistence` requires `no-fp-infinite-simple-group-is-amenable`.

Never write a `requires: []` route into this claim.

**Reading.**
- "Find" asks for an example. A proof that no finitely presented infinite simple
  group is amenable resolves the problem negatively, for both readings.
- The parenthetical "(or F∞)" names a stronger variant, since type F∞ implies
  finite presentation. A finitely presented example answers the problem as
  printed. If it is not known to be of type F∞, the root body must say that the
  F∞ variant stays open when the construction route fires.
- A finitely generated infinite simple group is not elementary amenable (Chou,
  1980; not re-read here). So an example is also a finitely presented amenable
  group that is not elementary amenable. That is the finitely presented form of
  Problem 1.12; 1.12 itself asks for type F∞.

**Attribution.** The list says that problems added after June 15, 2023 carry the
date added. Problem 1.10 carries no date, so it was on the original list of
June 15, 2023. The finitely generated version is Kourovka Problem 15.5
(de la Harpe), answered by Juschenko–Monod (arXiv:1204.2132) with derived full
groups of minimal subshifts. Those groups are never finitely presented (Matui,
arXiv:math/0404117; Grigorchuk–Medynets, arXiv:1105.0719, through LEF). Before
this root the region recorded no written source for the finitely presented
question (`fp-infinite-simple-amenable-group`, Status); Zaremsky's list is one.

**Graph state, 2026-09-13.** Every finitely presented infinite simple group
recorded in the graph is non-amenable. The live candidate is
`D([[Z^2 ~ Omega_U]])` for Labbé's minimal aperiodic Wang shift, through the
route `fp-simple-amenable-via-labbe-shift-full-group`. It is gated by two open
claims, `labbe-shift-derived-full-group-is-amenable` and
`labbe-shift-derived-full-group-is-finitely-presented`. The Penrose tiling group
has the same profile.

## Attempts

- 2026-09-13: root created by lane z1-10-simple-amen-build (construction side);
  lane z1-10-simple-amen-block works the nonexistence side. The recorded
  obstructions (compressible hosts, periodically approximable subshifts,
  residually finite actions, hosts containing V, Kazhdan groups) and the live
  candidates are listed under `fp-infinite-simple-amenable-group`, Attempts.
