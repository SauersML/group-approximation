---
rg: 2
id: atlas-multiplicity-two-joint-kernel-slice-proof
kind: route
title: Quotient the repeated H6 commutant and bit-pack every gauge
target: atlas-multiplicity-two-joint-kernel-slice-is-empty
requires:
  - atlas-l44-h6-has-thirty-frobenius-frames
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
  - atlas-q14-adds-stratified-thirteenth-double-coset
artifacts:
  - experiments/atlas_a4_repeated_module_probe.py
  - experiments/atlas_a4_repeated_module_dataset.py
  - experiments/atlas_a4_repeated_module_screen.cpp
  - experiments/atlas-a4-repeated-module-screen.json
---

Bit-packed Gaussian elimination computes the H6 and A8 commutant algebras
inside `Mat8(F2)`.  Enumerating their units gives orders `120960` and six;
left-coset marking gives exactly `20160` chart-distinct gauges.  For each of
the `1262` seed lifts, the C++ replay rejects on the first failed H18 edge,
then evaluates collision and q14 by literal `8 x 8` multiplication.

As an internal orientation check, exactly `180` gauge cosets admit an
F4-linear representative.  Their packet counts reproduce the independent
L4(4) screen exactly: `2754` packet points, zero collision points, and q14
counts `729`/`486` in inner/graph parity.  Five seed intertwiners are also
checked independently in Sage after restriction of scalars.  Assertions pin
all centralizer orders, survivor counts, and `(M2J1)`.
