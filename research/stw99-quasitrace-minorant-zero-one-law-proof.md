---
rg: 2
id: stw99-quasitrace-minorant-zero-one-law-proof
kind: route
title: Hahn-Banach minorant of the dimension function, CAP by complete additivity, separating by unitary conjugation, then Gow Cor. 3.10
target: stw99-quasitrace-minorant-zero-one-law
requires: []
artifacts:
  - research/artifacts/stw99-quasitrace-minorant-zero-one-law-2026-09-17.md
---

Sections 2 and 3 of the artifact. Imported results:

- Gow arXiv:2601.04431v2, Cor. 3.10: separating CAP states force W*.
- Gow §2.3: `tau = D` is completely additive on projections in a `II_1` AW*-factor.
- Kaplansky dimension theory for finite AW*-factors.
- Haagerup arXiv:1403.7653, Cor. 3.4 and Lemma 3.5: monotonicity, unique matrix
  extension, square-root subadditivity.

Steps:

1. `S(a) = inf{ sum c_i D(p_i) : sum c_i p_i >= a }` is finite and sublinear on
   `M_sa`, and vanishes on `-M_+`.
2. Hahn–Banach gives a positive `phi <= S` with `phi(1) = S(1)`.
3. `0 <= phi(p - sum_F p_i) <= D(p) - sum_F D(p_i) -> 0`, so `phi` is CAP.
4. Given `p != 0`, take `p' <= p` with `D(p') = 1/m`, and unitaries `u_j` with
   `sum_j u_j p' u_j* = 1`. Some `phi∘Ad(u_j)` is positive on `p`.
5. Gow Cor. 3.10 gives W*. For W*, `tau` is the normal trace, so every cover has
   mass `>= 1`.
6. C-subadditivity and pinching bounds give mass `>= 1/C`, through the Gram
   matrix `[b_i^{1/2} b_j^{1/2}]` of a cover.
