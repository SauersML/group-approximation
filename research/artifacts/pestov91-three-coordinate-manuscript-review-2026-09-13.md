# Rank three, return localization, and the low-rank boundary

2026-09-13. Draft manuscript update in the group-approximation repository.
These additions are written proofs, not new Lean formalizations or a
release attestation. No literature-priority claim is made.

## Mathematical change

- A bilateral shift corrected by a three-cycle on negative wandering
  levels creates a finite central compression defect in GL_3. The exact
  F2 general-linear MF radical therefore starts at rank three. The
  unrestricted elementary-group theorem still starts at rank four:
  the new compressor need not be elementary.
- A single involution in 1+I simultaneously moves any finite transient
  coefficient pattern into any full clopen return corner. This replaces
  normal-generation bookkeeping by one conjugation.
- The resulting general-linear rank budget is nk>=3. The manuscript
  states the consequences directly: no fixed points gives all matrix
  ranks n>=2, and no periods one or two gives the unit group. Over F2
  the full MF radical is the core restriction kernel. Aperiodic systems
  need no external matrix amplification.
- The two-ended compactification of the shift has LEF units but a
  non-directly-finite crossed product and non-MF GL_3. This prevents
  dropping the dynamical hypothesis from a universal unit statement.
- Fixed cores make every Kazhdan subgroup of GL_2 finite; cores with
  periods at most two do the same for units. The proof uses the locally
  finite kernel and Guentner--Higson--Weinberger, Theorem 4. Thus the
  entire Kazhdan compression criterion is inert in these cases. This
  does not decide whether GL_2, or unrestricted EL_3, is MF.

The full arguments and primary-source citation are in
[the proof artifact](pestov91-three-coordinate-compression-and-involution-localization-2026-09-13.md).

## Validation

All execution ran on MSI, using shared storage and warm caches.

- The [finite matrix audit](pestov91-three-coordinate-matrix-receipt-2026-09-13.json)
  passed 576 identities in characteristics 2, 3, 5 and 7, plus 142
  involution-placement blocks, in 0.052049 seconds. It deliberately
  detects the failure of proper compression in the finite cycle models;
  it is not a check of the infinite compression theorem.
- The [claim-manifest audit](pestov91-three-coordinate-manuscript-receipt-2026-09-13.json)
  passed in 0.206 seconds. There are three new paper-proof statements,
  one strengthened paper-proof statement, and 31 unchanged prior
  statements, for 35 total. All Lean badge mappings remain unchanged;
  only the 27 cited modules were indexed.
- The [CAIRN dependency audit](pestov91-three-coordinate-cairn-receipt-2026-09-13.json)
  passed check and preview with no errors in 36.123 seconds, against
  base `09b3b57e4db99234ac497799733927aa58bb5c84`. All five new claim
  targets and the existing core-radical claim are `ESTABLISHED` in the
  dependency graph. This status records graph support, not independent
  verification of the mathematics. The archived delta predates this
  review, its own audit receipt, and the final rendered PDF; none changes
  the checked mathematical nodes or proof source.
- LuaLaTeX produced a 31-page draft with no overfull boxes, unresolved
  references, or rerun request. The existing bibliography has one
  underfull paragraph. A bounded initial multi-pass build was interrupted;
  its partial auxiliary file was isolated and complete individual passes
  then finished successfully using the same warm cache.

Visual review: all 31 pages were inspected in contact sheets, and pages
19--24 were inspected individually. The new compression identities,
radical formulas, localization lemma, return proof, example, and rank
boundary are legible, with no clipping, overlap, or broken displays.

Final source SHA256:
`0c4ada3c150d08fbf1cdf30444d865ac7c43091369cf78efa9e5ed5d238e3f1e`.

Final PDF SHA256:
`786b5597c31f5e806e7b64dbef576fe9bb36fb7be6babd2b67d20e3cadba2c55`.
