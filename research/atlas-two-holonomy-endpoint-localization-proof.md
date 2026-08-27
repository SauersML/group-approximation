---
rg: 2
id: atlas-two-holonomy-endpoint-localization-proof
kind: route
title: Compare the bridge matrices with the canonical packet component labels
target: atlas-two-holonomy-endpoint-localization
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-t30-is-one-parabolic-c3-bridge
artifacts:
  - experiments/atlas_a4_packet_component_audit.py
---

The component audit extracts the ten packet labels directly from the thirty
radius-five pair cubes, orders them by their exact `4 x 4` binary matrices,
and partitions their pair graph into its two connected components.  It then
compares the four frozen bridge matrices `h,k,z,b` with those two label sets.

Exact byte comparison places `h` in component zero and `k,z` in component
one, while `b` belongs to neither component.  The existing order and center
audits identify `h,k,z` as order-three elements and `z` as the central `C3`
letter.  Substitution into `c=hk` and `a=zb` proves the stated endpoint
description.  No representation or numerical approximation is involved.
