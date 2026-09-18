---
rg: 2
id: zaremsky-3-05-four-strand-burau-faithful
kind: claim
title: "Zaremsky Problem 3.5 resolved: is the 4-strand Burau representation faithful?"
root: true
artifacts:
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part1.md
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part2.md
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3 ("Matrix groups,
braid groups, etc"), Problem 5, verbatim: "Is the 4-strand Burau
representation faithful?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-05-by-yes` requires
  `four-strand-burau-representation-is-faithful`.
- **No**: `zaremsky-3-05-by-no` requires
  `four-strand-burau-representation-has-nontrivial-kernel`.

Never write a `requires: []` route into this claim.

**Reading.** The Burau representation of the braid group `B_n` sends the
standard generator `sigma_i` to the matrix `[[1-t, t], [1, 0]]` on
coordinates `i, i+1`, and to the identity elsewhere. This gives
`B_n -> GL_n(Z[t, t^{-1}])`. Over `Q(t)` it splits off a trivial summand, and
the reduced and unreduced versions have the same kernel. The question asks
whether this homomorphism is injective for `n = 4`.

**Known before the list.**

- Faithful for `n <= 3` (Magnus–Peluso, 1969).
- Not faithful for `n >= 9` (Moody, 1991), for `n >= 6` (Long–Paton, 1993),
  and for `n = 5` (Bigelow, 1999).
- The list (July 12, 2026) records `n = 4` as open.

## Attempts

- **2026-09-13, the preprint.** arXiv:2607.05283v1 (V. Bharathram,
  J. S. Birman, T. E. Brendle; posted July 6, 2026; 26 pages; unrefereed; no
  later version or withdrawal as of September 13, 2026) claims the Yes
  answer.
- **2026-09-13, line-by-line check: GAP.** Details in
  `research/artifacts/zp-burau-n4-verification-2026-09-13-part1.md` and
  `-part2.md`.
  - Verified: the reduction to the Brunnian subgroup, Moody's criterion,
    parity implying no cancellation, and the new proof for `n = 3`.
  - Not verified: the `n = 4` core.
    - Lemmas 6.2–6.3 are supported by figures only.
    - Proposition 6.4's last step asserts, without proof, that the modified
      push map still satisfies parity and strictly increases the
      intersection count. Together those facts amount to the theorem for the
      braid in question.
- **The Yes side in Cairn.**
  - Lane z3-05-burau-theory factored the preprint into
    `four-strand-burau-faithful-via-brunnian-braids`. That route requires
    `burau-four-faithful-iff-faithful-on-brunnian-braids`, which is
    established independently through Long's theorem, and
    `brunnian-four-braids-avoid-burau-kernel`, which is open.
  - The unverified step is the open claim
    `brunnian-four-braids-admit-parity-correcting-push`. It feeds
    `brunnian-four-braids-have-five-strand-moody-witness` through the route
    `five-strand-moody-witness-via-parity-correction`.
- **The No side.** An exhaustive meet-in-the-middle search in the free
  point-pushing subgroup `K_4` (lane z3-05-burau-search, MSI) found no Burau
  kernel element of free length at most 24 in the basis `A_{14}, A_{24},
  A_{34}`: `burau-kernel-avoids-short-point-pushing-braids`, established by
  machine computation with exact re-checking and controls.
- Neither answer route is complete.
- **Obstruction: evaluation-point repairs of the parity step die (sw-095, 2026-09-17).** Replacing
  parity by "no Moody cancellation at a fixed point `t_0 ∈ C^×`" cannot certify faithfulness on
  `Brun_4`, at any `t_0`. For `t_0/|t_0|` of odd or infinite order the clean counts see only
  `𝕄(1)` and are blind to all of `[P_n, P_n]`. For order `2^a r` they are blind to an explicit
  nontrivial Brunnian braid `Ψ_{Φ_{2^a}}`, with conjugate powers and five-strand pushes allowed.
  Fixed finite jets of `𝕄` at roots of unity are blind too:
  `brunnian-4-braids-meet-cyclotomic-burau-congruence-kernels`,
  `clean-moody-counts-are-blind-at-every-evaluation-point` (artifact
  `research/artifacts/burau-cyclotomic-blindness-2026-09-17.md`). Surviving classes: evaluation
  points that depend on the braid with unbounded 2-power order, and invariants that are not
  cyclotomic residues of `𝕄` (full no-cancellation, extreme exponents, weighted counts).
