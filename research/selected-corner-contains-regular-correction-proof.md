---
rg: 2
id: selected-corner-contains-regular-correction-proof
kind: route
title: Tensor an arbitrary regular microstate with one exactly reducing bit
target: selected-corner-correction-contains-regular-correction
requires: []
---

Given any regular-trace lattice microstate, tensor every generator with the
identity on `C^2` and select the first coordinate.  Compression returns the
original tuple exactly, while the selector has trace one half, commutes with
all generators, and has the same normalized mixed word traces.  Therefore a
uniform selected-corner correction theorem corrects every regular lattice
microstate.

For the native four atoms, expand their mixed trace with a lattice word into
the four canonical group traces in `(SCC5)`.  All vanish away from the
identity, so the normalized corner trace is regular.  This excludes the
amenable-limit character-rigidity theorem as a source of the desired corner
correction.
