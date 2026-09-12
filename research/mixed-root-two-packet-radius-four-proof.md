---
rg: 2
id: mixed-root-two-packet-radius-four-proof
kind: route
title: Enumerate exact Bergman forms, filter by odd intersection, and evaluate every survivor
target: mixed-root-two-packet-radius-four-has-no-solution
requires:
  - two-packet-solutions-have-odd-intersection
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
  - research/artifacts/filter_two_packet_len4.py
  - research/artifacts/verify-kl-gate-c3-corner.py
---

`filter_two_packet_len4.py` enumerates all reduced words through the stated
length in eight involutory generators, canonicalizes their Leavitt values by
exact Bergman normal form, and retains the first word for every distinct
genuinely mixed value.  It asserts the candidate counts 204 and 1,254 at
lengths three and four.

For every ordered pair it computes the two packet supports and applies the
prerequisite's odd-intersection condition.  It asserts survivor counts 208
and 1,394.  For every survivor it then evaluates all four terms of the full
group-ring residue exactly over `F_2` and asserts that the residue is nonzero.
The enumeration contains no probabilistic or heuristic step.
