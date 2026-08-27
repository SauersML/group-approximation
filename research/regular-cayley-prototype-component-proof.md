---
rg: 2
id: regular-cayley-prototype-component-proof
kind: route
title: Identify prototype connectivity with one generated subgroup
target: regular-cayley-prototype-components-have-fixed-size
requires: []
---

A path starting at `g` and using the edges `(RCP1)` ends at `g l` for some
word `l` in `D union D^-1`, hence remains in `gL`.  Conversely every
`l in L` is such a word, so every element of `gL` is connected to `g`.
Therefore the component of `g` is exactly `gL`.

If a set `F` is closed under all prototype edges, then for every `g in F` it
contains `gL`; hence it is a union of these components.  Connectedness makes
it one coset, proving the size assertion.

