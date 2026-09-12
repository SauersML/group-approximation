---
rg: 2
id: aut-f4-has-property-t
kind: claim
title: Aut(F_4) and Out(F_4) have Kazhdan's property (T)
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that imports the embedding of every Aut(F_n) into a finitely presented simple group; this imports Nitsche's computer-assisted proof that Aut(F_4) has property (T).
artifacts:
  - research/artifacts/aut-f4-property-t-status-2026-09-12.md
---

**ESTABLISHED (literature import, computer-assisted, unrefereed).**

> **Theorem 6.1 (Nitsche, arXiv:2009.05134v3).** Aut(F_4), the automorphism group
> of the free group over four generators, satisfies property (T).

Out(F_4) = Aut(F_4)/Inn(F_4) is a quotient of Aut(F_4). Property (T) passes to
quotients, so Out(F_4) has property (T) as well.

**The complete answer for Aut(F_n).**
- **n = 2, 3: no (T).**
  - Aut(F_2) maps onto GL_2(Z), which is virtually free.
  - Aut(F_3) maps onto Out(F_3), which McCool showed is virtually residually
    torsion-free nilpotent. Grunewald–Lubotzky showed Aut(F_3) is large.
  - Both are quoted from the introduction of Kaluba–Kielak–Nowak; the original
    papers were not read.
- **n = 4:** Nitsche, Theorem 6.1.
- **n = 5:** Kaluba–Nowak–Ozawa, Theorem 1 and Corollary 2.
- **n ≥ 6:** Kaluba–Kielak–Nowak, Theorem 5.9.

**How the proof works.**
- It passes to the index-2 subgroup SAut(F_4), with Nielsen generators.
- It finds a decomposition Δ² − εΔ = Σ ω_i* ω_i with ε > 0 on a support T strictly
  between the balls S² and S³. The 2-ball used for n ≥ 5 is too small, and S³
  gives an SDP too large to solve.
- The witness is published as Zenodo record 7065231. The article attaches a SAGE
  script that verifies it with interval arithmetic.

**Caveats.**
- The interval-arithmetic verification was not rerun in this repository.
- arXiv lists no journal reference for 2009.05134.
- Nitsche's arXiv:2312.13917 proves (T) without a computer only for all but
  finitely many n. So n = 4 still rests on the certificate.

The artifact records the verbatim statements, and a scan showing that the nearby
computational spectral-gap questions are either already settled or explicit-constant
problems.
