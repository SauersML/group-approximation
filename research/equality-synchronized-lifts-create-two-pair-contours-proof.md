---
rg: 2
id: equality-synchronized-lifts-create-two-pair-contours-proof
kind: route
title: Close two lifted pair edges through their connected equality fibers
target: equality-synchronized-lifts-create-two-pair-contours
requires:
  - expander-cloud-reduction-preserves-pauli-dimension-gap
---

Two distinct lifts `u_0--v_0` and `u_1--v_1` of one logical pair edge have
their X endpoints in one connected equality fiber and their Z endpoints in
one connected equality fiber.  Simple paths in those two disjoint fibers,
together with the lifted edges, form a mixed cycle with exactly two pair
edges.  Its reduced relative form has at most four syllables, while its whole
ordinary contour contains only two `P` letters.  This proves both the relative
minimum-length failure and the balanced `(BG2)` failure.

The dimension assertion is the expander-cloud theorem itself applied after
regularly duplicating the old pair-test distribution: choose one
representative per connected logical fiber and replace test endpoints on the
same Hilbert space.  Thus dimension preservation and the contour obstruction
hold simultaneously.

