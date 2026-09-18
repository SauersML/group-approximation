# SMART height-3 renormalization: first search (lane gq-affq, 2026-09-18) — CORRECTED

**Correction (same day).** The first version of this note (0e1078f57) concluded that a
tape-cell deletion cannot be a brick-local renormalization. **That conclusion was wrong, and so
was the argument for it.**
- *Structural claim, retracted.* In the moving-tape coding the two Cantor coordinates are the
  tapes read outward from the head, so deleting the neighbour of the head is the bounded prefix
  replacement `P(q,c_0) D(c_1) -> P(q,c_0)`. Every prefix replacement `u w -> v w` with
  `|u| != |v|` shifts the tail relative to the head, and so does every move of `F`; this is
  allowed in `2V`. (Pointed out by lane gq-nv-obstruct.)
- *Measured "collapse", retracted.* The run at equality radius `R_EQ = 150` exceeded the window
  `W = 120` that the edit materialised. Beyond `W` the edited configuration drew its cells lazily
  at random, independently of the original, so the comparison failed for a reason unrelated to
  the mathematics. It was a harness bug.

The explicit rule of `smart-induced-map-has-brick-local-height-3-renormalization` has since been
validated on full finite tapes with whole-array comparison:
`research/artifacts/gq-affq-smart-renormalization-validation.md`.

## What remains valid from the first search

Compute on MSI only (`/projects/standard/hsiehph/sauer354/gqsrc/gq-affq/`), single core,
python3, fixed seeds. SMART table from Callard–Salo arXiv:2208.00685v3 `distortion-1-smart.tex`.

| run | window radius `r` | `R_EQ` | result | status |
|---|---|---|---|---|
| run1 (E1) | 0–8 | — | substitution phase unambiguous from the radius-1 window over 3600 visits | valid |
| phi_r2 | 2 | 40 | a radius-2 deletion rule, all 204 windows nonempty; `φ S^3 = S φ` ok 3524, bad 0; preimages {1: 284, 0: 16} of 300 | valid within `R_EQ = 40 < W` |
| phi_r3 | 3 | 40 | 886 windows nonempty; undersampled | inconclusive |
| phi_r2_deep | 2 | 150 | "all rules collapse" | **invalid: `R_EQ > W` harness bug** |

The 16 missing preimages in phi_r2 come from the rule table's unsampled windows and from edits
that coincide on the finite window; the exact rule has an explicit inverse (validation note).
