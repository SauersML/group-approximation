---
rg: 2
id: one-steinberg-group-contains-every-gl-n-q-proof
kind: route
title: Kill K_2 of matrix rings over Q with Cuntz families of every size, then lift St_4(M_m(Q)) into St_4(S)
target: one-steinberg-group-contains-every-gl-n-q
requires:
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - research/artifacts/gq-referee-a-one-steinberg-group-contains-every-gl-n-q.md
  - research/artifacts/gq-referee-b-one-steinberg-group-contains-every-gl-n-q.md
  - research/artifacts/gq-referee-c-one-steinberg-group-contains-every-gl-n-q.md
---

Direct proof, written in the target under `## Attempts`, item 1, steps (a)–(e) (lane gq-deep-free-1).
Referees a, b and c returned PASS, conditional on the classical `K_2` inputs listed below.

**Graph inputs.**
- `steinberg-finite-presentation-and-kazhdan-theorem` gives finite presentation of `St_4(S)` for finitely
  presented `S`, which is part 3.
- Parts 1 and 2 hold for every ring `S` with `Q` and a Leavitt pair and need no graph node. No specific ring
  is required: the explicit hosts `D` and `R_L` enter only through the routes
  `gl-n-q-explicit-via-st-4-of-divisible-ring` and `gl-n-q-explicit-via-st-4-of-resolvent-ring`.

**Literature inputs.** These are cited in the proof and are not graph nodes:
- centrality of `K_2(n, A)` for `n >= sr(A) + 2` (Voronetsky, arXiv:2004.08551v2, introduction, citing
  Dennis, LNM 353), with Bass's `sr = 1` for semisimple Artinian rings;
- Kervaire's central closedness of `St_n` for `n >= 5`;
- Matsumoto's `K_2(n, F) = K_2(F)` for a field and `n >= 3`;
- Tate's computation showing `K_2(Q)` is torsion (Milnor, *Introduction to algebraic K-theory*, §§11–12).

**Rank.** The rank-four finite presentation is the Krstić–McCool import inside
`steinberg-finite-presentation-and-kazhdan-theorem`; gq-referee-c passed `n = 4` as a literature import.
Its citation-free form, `steinberg-groups-of-fp-rings-are-fp-in-rank-five`, covers only `n >= 5`. It is not a
requirement here, because the target is about `St_4`. The ring `R_L` of
`leavitt-resolvent-ring-is-fp-and-contains-q` serves equally as `S`; that host is wired through
`gl-n-q-explicit-via-st-4-of-resolvent-ring`.
