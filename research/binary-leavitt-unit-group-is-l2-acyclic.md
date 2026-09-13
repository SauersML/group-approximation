---
rg: 2
id: binary-leavitt-unit-group-is-l2-acyclic
kind: claim
title: Every L²-Betti number of the binary Leavitt unit group vanishes
distinct_from:
  binary-leavitt-unit-group-integrally-acyclic: that is vanishing of integral homology H_n(R^x; Z); this is vanishing of the von Neumann dimensions of H_n(R^x; N(R^x)). Neither implies the other in general (Higman's acyclic group has positive second L²-Betti number, and Z is L²-acyclic but not acyclic), and the proofs differ at the stabilizers.
  binary-leavitt-unit-group-has-tt-mod-t: that rigidity statement gives property (T) and hence only β_1^(2) = 0; this is vanishing in every degree.
---

**ESTABLISHED (proved on paper, unreviewed).** Let `R = L_(F_2)(1,2)`. Then
`β_n^(2)(R^x) = 0` for every `n >= 0`.

**Profile.** `R^x` is an infinite, finitely presented, simple group. It is integrally acyclic,
L²-acyclic, Kazhdan and nonsofic.

**Proof.**
1. For `n >= 0` put `r = n + 3`. The frame complex `X_r(R)` is `(r-3)`-acyclic
   (`binary-leavitt-frame-complexes-are-highly-acyclic`), and `R` is infinite.
2. `frame-acyclic-rings-have-low-degree-l2-acyclic-gl` gives `β_n^(2)(GL_r(R)) = 0`.
3. A complete prefix code with `r` leaves identifies `M_r(R) ≅ R` as rings, so
   `GL_r(R) ≅ R^x`.

The vanishing range grows with the rank, and Leavitt self-similarity makes every rank the same
group. Artifact: `research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md`.

**Analogue for `V`.** The subgroup `V` is known to be l²-invisible (Sauer--Thumann,
arXiv:1304.6843, Theorem 1.1), which is stronger. The unit group is not a local similarity
group, and non-reduced vanishing for it stays open.

Route: `binary-leavitt-unit-group-l2-acyclic-proof`.
