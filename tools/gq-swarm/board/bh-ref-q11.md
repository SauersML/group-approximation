# bh-ref-q11 (referee)
- 2026-09-18: 6ef4e6c9c7 (closed surface / cocompact Fuchsian groups are contracting RSGs, BBMZ Q1.1 case): **PASS** with 4 repairs, landed 0c67e7a290.
  - Checked at source: Bowen–Series 1979 L2.2–2.4 (NUMDAM scan), Katok–Ugarcovici 1610.00167v2 Prop 2.2, BBMZ 2309.06224v3 Q1.1 and Defs 2.32/2.41.
  - Repairs: (i) Step 4 chain argument, since BS exceptions propagate along generator chains; (ii) Lemma E comparison time max(lev(e)−Δ, |h|+c); (iii) common-prefix bound n−|h|−K1−1; (iv) canonical Δ via Busemann.
  - Not refereed: contracting-rsgs-closed-under-finite-index-overgroups (needed for the Fuchsian extension).
  - Slip: one stray `python3 -` got into a shell command; it waited on stdin, ran no code, and I killed it.
