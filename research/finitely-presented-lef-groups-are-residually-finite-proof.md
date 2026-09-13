---
rg: 2
id: finitely-presented-lef-groups-are-residually-finite-proof
kind: route
title: A LEF partial embedding of a relator ball extends to a finite quotient separating a given element
target: finitely-presented-lef-groups-are-residually-finite
requires: []
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

Complete proof: artifact Section 3 (Lemma P).

1. Take `Γ = ⟨S | R_0⟩` with `S = S^(-1)`, and `g ≠ e` given by a word `w`. Let `B` be the word-metric ball of radius at
   least the lengths of `w` and of every relator.
2. LEF gives an injective `φ : B -> Q` into a finite group, multiplicative on `B`. So `φ(e) = e` and
   `φ(s^(-1)) = φ(s)^(-1)`.
3. `θ(s) = φ(s)` defines a homomorphism on the free group. By induction on prefixes, `θ(v) = φ(v̄)` for words whose prefixes
   lie in `B`.
4. Relators map to `φ(e) = e`, so `θ` factors through `Γ`. And `θ(w) = φ(g) ≠ e` by injectivity.
