---
rg: 2
id: slofstra-solution-group-collision
kind: route
title: Use Slofstra's solution-group involution as the sofic-radical half
target: sofic-radical-hyperlinear-survivor
requires: []
artifacts:
  - notes/NOTEPAD.md
---

# Use Slofstra's solution-group involution as the sofic-radical half

A natural candidate, and the reason it fails. Dead.

## The idea

The radical-collision criterion needs a countable group `H`, a nonidentity
`x in Rad_sof(H)`, and one homomorphism to a hyperlinear group not killing
`x`. Slofstra's solution group `S` (arXiv:1703.08618v2, Proposition 5.1) looks
like an unusually good source for the *radical* half: its distinguished
central involution `J` is invisible in every exact finite-dimensional
representation, and the group comes with a rich supply of Connes-embeddable
images on the detector side, so both halves appear to be in place at once.

## Why it fails

`J` is not in the sofic radical. `slofstra-involution-not-sofic-radical`
constructs a homomorphism from `S` to a metric ultraproduct of finite
symmetric groups with `Theta(J) != 1`, by making every finite-coordinate
construction in Slofstra's proof permutation-valued and repairing the one
approximate involution by an `o(|X_n|)` cycle surgery.

So the candidate fails on the half that looked secure. The detector side was
never the problem here.

## The general lesson this route encodes

The appeal of `J` rested on an invalid inference — that invisibility in exact
finite-dimensional representations implies membership in the sofic radical.
The corpus states the gap explicitly: *"exact finite-dimensional invisibility
alone does not imply this."*

That is now the **second** candidate eliminated by exactly this mistake; the
first was the literal non-MF mark (`literal-clifford-ce-model`), which turned
out to be visible in a sofic group as well. Both times the word was invisible
to exact finite-dimensional representations and visible in an approximate
model. Any future candidate should be tested against a permutation-ultraproduct
construction *first*, since that is the cheap half, before effort is spent
building a hyperlinear detector.
