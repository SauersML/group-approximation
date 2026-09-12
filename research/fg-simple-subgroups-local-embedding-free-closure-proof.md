---
rg: 2
id: fg-simple-subgroups-local-embedding-free-closure-proof
kind: route
title: Push a finitely generated simple subgroup through each O3-free permanence operation until it lands in a sofic group
target: fg-simple-subgroups-of-local-embedding-free-closure-are-sofic
requires: []
artifacts:
  - research/artifacts/fg-simple-groups-and-the-permanence-closure-2026-09-12.md
  - research/artifacts/gottschalk-table-realization-and-evasion-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Derivation: Section 1 of the first artifact. It is the stage induction of
`permanence-closure-evasion-proof` with the finite presentation removed. That
hypothesis is used there only for (O3), which this closure omits.

- **O1, O2.** Finite generation puts `Q` in an earlier stage.
- **O4, O6, O7.** `Q ∩ kernel` is normal in `Q`.
  - If it is trivial, `Q` embeds into the base.
  - Otherwise `Q` lies in the kernel. A nontrivial site projection onto a residually
    finite group (O4), or soficity of the kernel (O6, O7), makes `Q` sofic.
- **O5.** The fold kernel acts freely on the Bass–Serre tree, so it is free and
  contains no infinite simple group. `Q` embeds into the fold target.

**Verification.** `w3-vf-positive` passed this route (Section 4.1–4.2 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`). Trust note for O6: soficity of graph products of LEF lamps rests on Ciobanu–Holt–Rees, or on Green's residual finiteness of graph products of finite groups; no node records either.
