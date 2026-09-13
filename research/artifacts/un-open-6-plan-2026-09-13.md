# un-open-6 plan: the arithmetic face of the paradox/measure dichotomy

Lane `un-open-6`, 2026-09-13, open-ended (lens: quantum and complexity). Unreviewed.

## 0. The chosen target

The repo classifies approximation properties of groups by arithmetical complexity:
`lef-of-finite-presentations-is-pi2-complete` (LEF_fp is Π⁰₂-complete), `lef-recognition-has-a-pi2-upper-bound`,
`fixed-mf-radical-membership-is-sigma2-complete`. The UN dichotomy says that for the Kazhdan elementary groups
over crossed products of minimal topologically free free-group Cantor systems, the approximation type is decided by
ONE dynamical bit: an invariant probability measure exists (LEF in every rank) or not (no MF quotient from rank 2n).

**Target.** Measure the complexity of that bit for effectively presented systems, and show that the Tarski
dichotomy lowers the complexity of the approximation type.
- (A) For an effectively closed subshift X_e of a finitely generated group with solvable word problem, "X_e carries
  an invariant probability measure" is Π⁰₁, uniformly in the index e (a compactness argument over finitely many
  linear programs).
- (B) On the promise class of effectively closed minimal topologically free F_r-subshifts, "EL_N(LC(X_e,F_q)⋊F_r)
  is LEF for every N ≥ 3" coincides with a Π⁰₁ set, and its failure ("no nontrivial MF quotient from some rank on")
  with a Σ⁰₁ set. This contrasts with Π⁰₂-completeness of LEF on finite presentations.
- (C, open) Π⁰₁-completeness on that promise class: a uniformly effective family of minimal systems that carry an
  invariant measure iff a machine never halts.

## 1. Why it matters

- It is a concrete sense in which the dichotomy has power: a Π⁰₂ property collapses to a single universal
  quantifier over linear programs, because Tarski identifies "no finite model obstruction" with "a measure".
- The certificate structure is explicit on both sides: a finite paradoxical decomposition (Σ⁰₁ witness of the non-MF
  side) versus a consistent family of pattern-frequency LPs (Π⁰₁ witness of the LEF side). These are exactly the two
  kinds of finite data behind the non-MF paper (one-sided compressions) and the Pestov answer (towers).
- Hardness (C) would say the approximation type of these Kazhdan simple groups is undecidable even with the
  dynamics fully effective, with an exact position Π⁰₁ rather than Π⁰₂.

## 2. What this lane does NOT duplicate

- un-open-2 (the MF spectrum in the rank N), un-low-rank-band (3 ≤ N < 2n), un-rf-beyond-free (which acting groups),
  un-architect (root and flagship statement), un-stability-nonsofic: none treats arithmetical complexity.
- The repo's complexity ledger (LEF_fp, RF_fp, MF radical) treats general presentations; this lane treats the UN
  promise class and imports the dichotomy nodes as they stand (unreviewed where they are unreviewed).

## 3. Deliverables

- Artifact `research/artifacts/un-open-6-tarski-complexity-2026-09-13.md` with complete proofs of (A) and (B).
- Nodes: `effective-subshift-invariant-measure-existence-is-pi01` (+ proof),
  `effective-free-group-kazhdan-lef-type-is-pi01` (+ proof, requires the dichotomy nodes),
  `effective-free-group-kazhdan-lef-type-is-pi01-complete` (open, with Attempts and firewalls).
- Secondary lens, only if time: synchronous-game encodings of the ring relations as a quantum restatement of (M).
