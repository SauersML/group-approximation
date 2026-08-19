---
rg: 2
id: steinberg-hyperfinite-hs-stable
kind: claim
title: The binary Leavitt Steinberg cover is hyperfinitely HS-stable
distinct_from:
  leavitt-steinberg-hs-stable: That is the open branch selection in the full normalized-HS metric; this is the unconditional restriction of it to hyperfinite targets, which is proved and does not select the branch.
  leavitt-steinberg-hs-unstable: This constrains what any witness for that claim must look like; it does not deny one.
artifacts:
  - notes/NOTEPAD.md
---

For `U=St_5(L_(F_2)(1,2))`, hyperfinite Hilbert--Schmidt stability holds
unconditionally, in the sense of Dogon--Vigdorovich.  `notes/NOTEPAD.md:22220`:

> **Theorem (unconditional hyperfinite HS stability).**  The group `U` is
> hyperfinitely Hilbert--Schmidt stable in the sense of Dogon--Vigdorovich.

The operative consequence, `notes/NOTEPAD.md:22234`:

> Consequently any witness to the unstable branch must generate a genuinely
> nonamenable limiting von Neumann algebra.  Hyperfinite, AF,
> amenable-factor, and character-approximation constructions are completely
> closed for this group.

This is a **restriction**, not a branch selection: it constrains only the
amenable part of the trace simplex, and the fork lives entirely outside it.
Its value is as a fence.  Any proposed construction for
`leavitt-steinberg-hs-unstable` whose limit algebra is hyperfinite, AF, or an
amenable factor, or which proceeds by approximating a character, is refuted
before it is built.
