---
rg: 2
id: topological-full-group-derived-uniform-exponential-growth
kind: claim
title: Does the derived topological full group [[φ]]′ of an infinite minimal subshift have uniform exponential growth? (Cornulier, Bourbaki 1064, question 7)
---

OPEN (printed question). Cornulier, "Groupes pleins-topologiques [d'après Matui, Juschenko, Monod, …]", Séminaire Bourbaki 1064 (January 2013), arXiv:2002.09342, section "Problèmes et questions ouvertes", item 7, verbatim from the source:

> Le groupe $[[\varphi]]'$ a-t-il une croissance exponentielle uniforme? A-t-il un diamètre semi-libre (resp. sans torsion) uniforme (c'est-à-dire, existe-t-il un entier $N$ tel que pour tout système générateur, la $N$-boule contient un couple d'éléments engendrant librement un semi-groupe libre (resp. contient un élément sans torsion)?

A negative answer for some `φ` would give a finitely generated simple AMENABLE group of non-uniform exponential growth. Thompson's `V` (Sauer–Schesler 2026) is not amenable.

## Progress
- **NEGATIVE for dyadic substitution subshifts** (sk-cornulier-q7, 2026-09-13, unreviewed): `dyadic-substitution-derived-full-groups-non-uniform-growth`.
  - Statement: for every primitive substitution of constant length 2 with a non-periodic fixed point (Thue–Morse, period doubling), `[[φ]]′` has non-uniform exponential growth.
  - So there is a finitely generated infinite simple amenable group of non-uniform exponential growth (`simple-amenable-group-of-non-uniform-exponential-growth`).
- **NEGATIVE whenever constant dyadic towers have bounded induced alphabets** (sk-sturmian-growth, 2026-09-14, unreviewed): `dyadic-tower-subshift-full-group-non-uniform-growth`.
  - The reviewed dyadic proof uses only (H1) and (H2) at infinitely many scales `m`:
    - (H1) `X = ⊔_(i<2^m) T^iV_m` with `T^(2^m)V_m = V_m`;
    - (H2) a clopen partition of `V_m` of bounded size generating its clopen algebra under `T^(2^m)`.
  - The dyadic substitution theorem is the instance `V_m = ζ^m(X)`.
- **Still OPEN:** the question for general infinite minimal subshifts (e.g. Sturmian), and the clauses on "diamètre semi-libre / sans torsion uniforme".

## Attempts
- **Transfer of the elementary-group engine** (sk-free-8). For a constant-length-2 substitution subshift, `[[φ]]` contains the level permutations of the towers of height `2^n`, and the induced shift `T_(V_n)` at one fibre.
  - This supplies the analogs of types 1–3, and a cyclic type 4, which counts as `(2ℓ+1)` per point.
  - Dies at generation: level permutations and `T_(V_n)` generate only "uniform" elements, whose cocycle depends only on the level. Generating `[[φ]]′` needs a fibre-dependent generator (a finite-order element supported on a small clopen set inside one level).
  - The commutation of such a generator with the type-4 conjugates, and its count per point (it must have a finite or abelian fibre group), are not checked.
- **Sauer–Schesler's V proof** (arXiv:2605.30163 §§4–5) uses rigid stabilizers of cylinders in `V`. Its analog for `[[φ]]′` would use rigid stabilizers of clopen sets (Matui's local subgroups). Not attempted.
- **Commuting local generators** (sk-cornulier-q7, artifacts `research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part1.md` and `-part2.md`). This fixes the generation gap in the first attempt.
  - The fibre-dependent generators are partial 3-cycles over the disjoint letter cylinders, which commute, plus one shift pair `S ⊗ S^(−1)`. The per-point group is `(Z/3)^|A| × Z`.
  - Complements, commutators `[(1 2 3),(3 4 5)] = (1 4 3)` and shift-pair conjugation give every clopen 3-cycle. Cornulier's Lemme `eng_cb` then gives the whole `[[φ]]′`.
  - **Succeeds** when `X` is a tower of constant height `2^m` over a clopen copy of itself with a bounded alphabet (dyadic substitutions).
  - **Dies** for Sturmian and other systems without constant dyadic towers: the Grigorchuk-level identification needs `2^m` levels, and bounded-size letter partitions of the induced systems.
- **Why Sturmian subshifts escape** (sk-sturmian-growth, `research/artifacts/sk-sturmian-growth-plan-2026-09-14.md` §2).
  - A constant tower `X = ⊔_(i<N) T^iV`, `T^NV = V`, gives the continuous eigenfunction `Σ_j e^(2πij/N) 1_(T^jV)`. So every subshift with (H1) has rational continuous spectrum, and totally minimal subshifts (Sturmian, weakly mixing) never do.
  - What Sturmian `X_α` do have is Rauzy renormalization: two towers of heights `q_n, q_(n−1)`, with first-return system again Sturmian with a two-letter partition. So (H2) holds with `K = 2`, but on two heights.
  - Routes, recorded in the plan artifact §3:
    - (R1) a level model of intermediate growth on the hierarchical level sets `A_(n+1) = A_n^(a_(n+1)) B_n`;
    - (R2) Grigorchuk levels on a dyadic block inside each tower, with remainder levels absorbed by the base structure;
    - (R3) a uniform-growth proof when partial quotients grow fast.
  - Not yet attempted beyond the obstruction.
