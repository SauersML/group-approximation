---
rg: 2
id: bf-n-r-twist-invisible-braid-characters-in-sigma-infinity
kind: claim
title: "Characters of bF_{n,r} with a nonzero full-twist-invisible braid part lie in Sigma^infinity"
distinct_from:
  bf-n-r-twist-detected-characters-lie-in-sigma-infinity: that claim is proved and covers braid parts with nonzero full-twist value; this open claim is the complementary case, braid parts in W_0, which exist only for n >= 3.
---

For `n >= 3`, `r >= 1`: let `chi = pi^* psi + phi` with `psi` any character of
`F_{n,r}` and `phi` a nonzero element of the full-twist-invisible subspace
`W_0` (dimension `n(n-1) - 2`; see
`pure-braided-bht-braid-characters-dimension-n-n-minus-1`). Claim: `[chi]` lies
in `Sigma^infinity(bF_{n,r})`. For `n = 2` the claim is vacuous (`W_0 = 0`).

## Attempts

- 2026-09-13, reduction (proved, artifact
  `research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md` Lemma 5): it
  suffices that the restricted characters
  `Phi_k(A_{ij}) = phi(type(i, j, k))` of `PB_k` lie in `Sigma^j(PB_k)` for all
  large `k`. Meinert's criterion then runs on the same Stein-space band as for
  the twist-detected characters.
- Where it dies: `Phi_k` kills the full twist, the only central element of
  `PB_k`, so the central-element criterion is silent. What remains is a question
  about the higher BNSR invariants of pure braid groups for these specific
  "spread-out" characters. It is adjacent to Problem 1.9 (lane z1-09-pure-braid).
  Candidate tools: Meinert's criterion for `PB_k` acting on the curve complex of
  the punctured disk, whose multicurve stabilizers have central Dehn twists with
  values `sum over pairs inside a subset`; product formulas for the cabled
  stabilizers.
- Explicit test case (`n = 3`, artifact §4): `PPP(alpha,gamma) = (-1)^gamma`,
  `PEP ≡ 1/2`, derived `EEP = PEE = -1/2`, and `EPE = 1` for odd `r`, `1/2` for
  even `r`. The full-twist value is zero at every number of leaves.
- `Sigma^1` is settled (unreviewed): `bf-n-r-braid-nonzero-characters-lie-in-sigma-one`,
  via Koban–McCammond–Meier's `Sigma^1(PB_k)`. The open part starts at `Sigma^2`.
- A caution. The boundary-supported elements of `W_0` factor through a
  non-split quotient `Z wr_Omega F_{n,r}`, the permutational wreath product over
  the `n`-adic points, split by residue. There a lamp-counting character is in
  `Sigma^1` but, like base characters of `Z wr Z`, is a candidate to miss
  `Sigma^2`. Split-quotient transfer does not apply, so this is only a warning
  that the formula could fail at `m >= 2` for `n >= 3`.
