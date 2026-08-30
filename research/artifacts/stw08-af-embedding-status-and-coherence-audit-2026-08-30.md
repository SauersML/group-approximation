# STW VIII / IX(2): status and coherence audit (2026-08-30)

## Current-status check

Problem VIII remains open in the current primary sources checked.

- Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*,
  [arXiv:2506.10902](https://arxiv.org/abs/2506.10902), v2 with addenda through
  April 2026, states VIII as the open question whether every separable exact
  quasidiagonal C\*-algebra is AF-embeddable and states IX(2) as its faithful
  quasidiagonal-trace special case.
- Y. Liu, *Characterizing AF-embeddable C\*-algebras by representations*,
  [Acta Math. Hungar. 173 (2024), 139--153](https://doi.org/10.1007/s10474-024-01442-x),
  describes the same assertion as a major open problem and gives a
  representation-theoretic equivalence, not a solution.
- Moradi--Amini, *On locally finite-dimensional traces II*,
  [arXiv:2606.13924](https://arxiv.org/abs/2606.13924), proves new results on
  quasidiagonal and locally finite-dimensional traces but does not claim VIII
  or IX(2).
- Dadarlat, *AF-embeddings of residually finite-dimensional C\*-algebras*,
  [Muenster J. Math. 11 (2018), 211--216](https://www.uni-muenster.de/FB10/mjm/vol_11/mjm_vol_11_05.pdf),
  Theorem 1.1, proves UHF-embeddability for separable exact RFD algebras whose
  rational `K^0`-homology is locally finitely generated.  This is used below
  for a semiprojective positive class, not as a solution of VIII.

The February 2026 seminar announcement about AF embeddings for certain
decomposition-rank-one systems was not used as a theorem: no primary preprint
containing that result was located in the check.

## Exact gap exposed by the audit

Quasidiagonality gives c.p.c. maps to unrelated finite-dimensional algebras
which are asymptotically multiplicative and isometric.  An embedding into an
AF inductive limit requires more: after choosing connecting homomorphisms, the
successive maps must be summably close.  Block-summing independent models does
not repair this in operator norm, because every old bad block survives
isometrically under an injective connecting map.

For a faithful quasidiagonal trace, norm detection can be recovered from
faithfulness once multiplicative models are coherently connected.  The trace
version therefore isolates two missing compatibility requirements: connecting
homomorphisms between the finite-dimensional models and compatible traces on
those models.

The Cairn nodes attached to this audit prove both coherence criteria from
scratch.  They do not assert that exactness produces the missing coherence.
