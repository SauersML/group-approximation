---
rg: 2
id: copy-marker-pair-balance-forces-reiter-for-symmetric-sets
kind: claim
title: "For a symmetric finite set A containing e, near-balance of the copy-marker pair of A at window n yields an A-Reiter measure at an elementary window, with defect tending to 0 with the imbalance (CMR)"
distinct_from:
  thompson-f-copy-marker-coding-balances-without-reiter: that node establishes the coding identity, the failure for the non-symmetric set {e,a,b} and the free-group certificate for B_1; this is the open transfer for symmetric sets that the certificate supports but does not prove.
  thompson-f-ramsey-radius-double-gap-below-reiter-radius: that is RGAP₂, a comparison of the Ramsey radius with the coarse Reiter radius; this compares the coarse Reiter radius with the balance radius of one fixed measure pair, with no colorings involved.
  moore-ramsey-criterion-for-amenability: that is a qualitative criterion over all colorings of balls; this is a quantitative criterion for one pair of measures on G×G.
---

**OPEN.** Notation is as in `thompson-f-copy-marker-coding-balances-without-reiter`. For finite `A ⊆ G` with
`K = |A|`, the copy-marker pair is `α_A` = the law of `(g, g)` and `β_A` = the law of `(e, g)` on `G×G`, with `g`
uniform on `A`. Write `B_n` for the word ball of `G` with respect to a fixed finite generating set, and
`d_A(μ) = (1/K)Σ_{g∈A} TV(gμ, μ)` for the A-Reiter defect.

**Statement (CMR).** There are functions `δ_K: [0,1] → [0,1]` with `δ_K(η) → 0` as `η → 0`, and an elementary
function `f` (a bounded tower in `n` and `K` also suffices for the application), such that the following holds.
Let `A = A⁻¹ ∋ e` be finite and let `ν ∈ P(B_n × B_n)` have `TV(α_Aν, β_Aν) ≤ η`. Then some
`μ ∈ P(B_{f(n,K)})` has `d_A(μ) ≤ δ_K(η)`.

The converse is free: a measure `μ` with `d_A(μ) ≤ η` gives `ν = μ ⊗ δ_e` with the same imbalance at the same window
(target node, "Reiter measures balance it"). So CMR says that the balance radius of one fixed pair of measures on
`G×G` and the A-Reiter radius of `G` agree up to an elementary change of window and precision.

**The two prerequisites it splits into.** Each can fail on its own.
1. *Qualitative (CMR₀).* If `A = A⁻¹ ∋ e` generates a non-amenable group, then `inf_ν TV(α_Aν, β_Aν) > 0`.
   This is the statement that the one pair detects non-amenability. Parts C and D of the target node test it: it is
   false without symmetry (`{e, a, b}` in `F_2` balances at rate `4/(3N)`), and it holds for `A = B_1` in `F_2`,
   with bound `> 0.0736`.
2. *Quantitative in F (CMR_F).* In Thompson's group F with `A = B_M`, the extraction of a Reiter measure from a
   balanced coupling costs at most an elementary change of window. This is where F-specific geometry enters. The
   copy `F×F ≤ F` is undistorted, so a balancing measure for the pair in F restricts to one on the copy (target
   node, "Reiter measures balance it").

**Consequences.** CMR_F bounds the coarse Reiter radius of F by an elementary function of the balance radius of a
single pair of measures. For a single pair the quantifier swap is free. The imbalance `∫φ d(α_Aν − β_Aν)` is
bilinear in `ν ∈ P(window)` and in the test function `φ ∈ [0,1]^{window}`, and both ranges are compact and convex.
So by minimax, "some `ν` balances every `φ` to within `η`" is equivalent to "every `φ` is balanced to within `η`
by some `ν`", at the same window.

The second form is a fine Ramsey statement for fractional colorings of the copy `F×F ≤ F`. Therefore CMR_F would
bound `CR` elementarily by the fine Ramsey radius at precision about `η`. That is the swap `∀E ∃ν` against
`∃ν ∀E` that blocks `thompson-f-ramsey-radius-double-gap-below-reiter-radius`, and every selector coding of the swap
dies there (Attempts of that node).

The bound is by the fine radius, not by the precision-1/2 radius `R`. So it bears on
`thompson-f-ramsey-amplification-needs-unbounded-tower-overhead` (¬AMP) directly. It bears on RGAP₂ only together
with an amplification step. Two further gaps remain between the fine Ramsey radius and this bound:
- fractional colorings versus sets;
- the choice of window.

Neither is checked here. In the sibling lane's vocabulary, which is still unlanded in worktree
`wf_4867ac15-691-57`, CMR_F is the single-function comparison that refutes the second-test-function gap. That
lane's node ids are not in this graph yet, so the link is stated only in prose here.

**Evidence.**
- *For.* The posterior identity (target, Part A) shows the pair forces `Y` to be stationary under every posterior
  `π_w`. For symmetric `A`, the cheap posterior splittings all die (target, "Invariant and dying step"). The segment
  splitting `[δ_e, u_T]` needs invariance under `⟨T⁻¹T⟩`, which has index at most 2 in `⟨T⟩`. The other splittings
  of `B_1` in `F_2` meet the unbalanced reflection pair, or else need invariance under the even subgroup.
- *For, numerically.* In `F_2` with `A = B_1`, the finite-window optima of the full pair (0.800, 0.450, 0.322,
  0.268, 0.239, 0.223 for `n = 0..5`) stay above the certified infinite-window bound 0.0736. So does the
  conjugation-versus-translation projection (0.188 at `n = 10`). All numbers are in
  `experiments/copy-marker-coding-2026-09-17/results.txt`.
- *Against, or at least unproved.* CMR₀ has been checked for exactly one symmetric set in one group. The B_1
  certificate works only after the projection `(x, w) ↦ wx⁻¹`, which forgets which coordinate carries the marker.
  A proof of CMR₀ in general has to control that projection, or avoid it, in groups without free-group normal forms.

**Falsifiers.**
- A finitely generated non-amenable group `G` and a symmetric `A ∋ e` generating it for which the pair balances,
  i.e. `inf_ν TV(α_Aν, β_Aν) = 0`. Natural first tests are:
  - `F_2 × Z` with its standard ball;
  - symmetric non-ball sets in `F_2`, such as `{e, a^{±1}, b^{±1}, (ab)^{±1}}`.

  The certificate pipeline (`projection_certificate.py` and `verify_certificate.py`) extends to other symmetric sets
  in `F_2`. It needs three edits: change the list `S`, restrict the symmetry group to the automorphisms that fix
  `S`, and, for words longer than one letter, lengthen the end pairs in the covering lemma.
- An amenable group, for example a lamplighter or an iterated wreath product, in which the balance radius of the
  pair for `B_M` is elementarily smaller than the Reiter radius for `B_M`. That would kill every uniform version of
  CMR and leave only an F-specific CMR_F.

## Attempts

- **2026-09-18 (swarm-0917-w11-w11-f-follow, reframing).** Node created from
  `thompson-f-copy-marker-coding-balances-without-reiter`. Done so far:
  - the posterior identity;
  - the non-symmetric counterexample, which is why symmetry is in the hypothesis;
  - the certificate for `A = B_1` in `F_2` (CMR₀ in one case).

  No transfer argument was attempted. The obvious one fails at a precise step. Take the posterior family
  `{π_w}` and try to extract one `w` with `π_w` close to `u_A` and `κ` nearly `π_w`-stationary. Averaging over
  `q` controls only `Σ_w q(w)‖π_w κ − κ‖`. Any `w` with `π_w ≈ u_A` then needs `μ_Z` to be nearly
  `A`-invariant near `w`, and that is itself a Reiter condition on `μ_Z`. So the extraction is circular unless one
  can iterate it with a gain. This lane found no gain.
