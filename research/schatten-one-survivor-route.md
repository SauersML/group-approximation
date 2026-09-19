---
rg: 2
id: schatten-one-survivor-route
kind: route
title: A Schatten-one model of the mark is a hyperlinear survivor
target: sofic-radical-hyperlinear-survivor
requires: [schatten-one-corner-detector, schatten-one-models-retaining-mark]
artifacts:
  - notes/TRUE_SCHATTEN_ONE_RADICAL_CORNER.md
---

## Why sufficient

`sofic-radical-hyperlinear-survivor` asks for a countable `H`, a nonidentity
`x in Rad_sof(H)`, and one homomorphism to a hyperlinear group not killing
`x`.  Given `schatten-one-models-retaining-mark` for the group `E` and its
central radical involution `z`, `schatten-one-corner-detector` produces
exactly that: the quotient map of `E` onto its image `L` in the tracial
ultraproduct of the negative corners, with `L` hyperlinear and the image of
`z` at normalized Hilbert--Schmidt distance `2` from `1`.  Take `H=E`,
`x=z`.

## Not a restatement of the target

The prerequisite is strictly stronger than the target and can fail while the
target holds.  The target asks only for some homomorphism to some hyperlinear
group retaining a sofic-radical element, with no norm attached; the
prerequisite asks for models in the unnormalized Schatten-one norm, a
hypothesis strong enough that Bachner--Dogon--Lubotzky *refute* it for
Deligne-type central extensions.  The genuine step is the lossless corner
conversion, which no reformulation of the target contains.

## Where this sits among the routes into that claim

It is a third input norm, alongside the operator-norm profile routes.  Its
attraction is that it needs no rate and no density: the corner conversion
`||A||_(2,r)^2 <= 2||A||_1` is lossless in an unnormalized norm.  Its cost is
that Schatten-one approximation is a strictly stronger hypothesis than
weak MF, and is *refuted* for Deligne-type central extensions.
