---
rg: 2
id: atlas-shortest-a4-triangle-packet-proof
kind: route
title: Exact radius-five enumeration exposes thirty pair-cube triangle relations
target: atlas-shortest-a4-triangle-packet
requires:
  - a4-triangle-zero-traces-force-regular
artifacts:
  - experiments/atlas_triangle_19243_packet.py
  - experiments/atlas_kernel_collision_enumerator.py
---

The replay first enumerates the complete radius-five kernel spanning tree by
exact binary Leavitt arithmetic.  It independently computes the word metric on
`GL_4(F_2)` from the six adjacent transvections and filters the `27256` tree
generators for words whose six free-product syllables alternate and repeat with
period two.

It retains precisely those with total `X`-length `9` and syllable orders
`{2,3}`.  There are exactly `30`.  Every retained word is already certified to
lie in the Leavitt kernel by the parent enumerator, and its literal form is
`(b_2 a_1)^3` or the factor-reversed version.  Together with `a^3=b^2=1` from
the exact chart packets, this is exactly the `A4` triangle presentation.

Finally the regular `A8` character vanishes on every nonidentity group element,
so both generators have trace zero.  The established A4 character-table lemma
therefore identifies every such joint representation as a multiple of
`Reg(A4)`.
