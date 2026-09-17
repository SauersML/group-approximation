---
rg: 2
id: fpbs-kazhdan-fixed-price-via-ideal-voronoi-contacts
kind: route
title: Contact-connected functional graphings in the Bernoulli closure give Kazhdan groups fixed price one
target: fpbs-kazhdan-groups-have-fixed-price-one
requires:
  - fpbs-functional-contact-criterion
  - fpbs-kazhdan-ideal-voronoi-contacts-connect
---

## Why sufficient

1. Let `Gamma` be a countably infinite Kazhdan group. Property (T) implies finite generation, so choose a finite
   symmetric generating set `S` not containing `e`.
2. `fpbs-kazhdan-ideal-voronoi-contacts-connect` supplies a free p.m.p. action `a ≺ b_Gamma` and a contact-connected
   Borel self-map `f` of the orbit relation of `a`.
3. These are exactly the hypotheses of `fpbs-functional-contact-criterion`, which returns fixed price one for
   `Gamma`.

## Decomposition

- The first prerequisite is OPEN, with a written proof awaiting a full referee panel.
- The second is OPEN, and it can fail: it is false for every group without fixed price one.
- The ideal Voronoi descent map (`fpbs-ideal-voronoi-descent-limit-exists`, OPEN with a written proof) is a candidate witness, but
  the route does not require it.
