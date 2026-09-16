# STW Problem I on three projections: swarm lane, 2026-09-16

Lane `swarm-stw01-three-projection-algebra`. Locked hole:
`stw01-three-projection-algebra-quasitraces-are-traces`. Outcome: **reduction**. Nothing new is
settled about Problem I.

## Setup

- **Target.** Every bounded 2-quasitrace on `P_3 = C^2 * C^2 * C^2 = C*(Z_2 * Z_2 * Z_2)` is a
  trace. It is equivalent to Kaplansky's quasitrace problem (STW Problem I), by the reviewed
  `research/artifacts/stw01-three-projection-universal-test-2026-09-12.md`.
- **Previous witness shape.** `sigma(g(r_1 r_2 r_1) + beta r_3)`, with a functional calculus `g` and a
  scalar `beta`. The target's recorded open attempt was "reduce to projections of equal trace,
  or to a free triple".
- **Notation.** `h_j = r_1 r_j r_1`, `D_sigma(a, b) = sigma(a + b) - sigma(a) - sigma(b)`, and
  `tau_e` is the canonical group trace. The automorphisms are `alpha` (`r_2 <-> r_3`) and
  `beta` (`r_2 -> 1 - r_2`, `r_3 -> 1 - r_3`).

## What was proven

Everything is in `research/artifacts/stw01-three-projection-corner-pair-test-2026-09-16.md`.

1. **Lemma 1.1 (corner dilation).** For `0 <= a, b <= 1` in unital `N`, the projections
   `P_1 = 1 (+) 0`, `P_2 = v_a v_a^*` and `P_3(theta) = v_b(theta) v_b(theta)^*` in `M_2(N)` satisfy:
   - `P_1 P_2 P_1 = a (+) 0` and `P_1 P_3 P_1 = b (+) 0`;
   - `P_2 ~ P_1 ~ P_3`;
   - `P_2 P_3 P_2` is equivalent to `w_theta^* w_theta (+) 0`, with
     `w_theta = a^(1/2) b^(1/2) + e^(i theta)(1-a)^(1/2)(1-b)^(1/2)`.
2. **Proposition 3.** `C*(r_1, h_2, h_3)`, with unit `r_1`, is the universal unital C*-algebra
   `V` of two positive contractions. The proof is complete and self-contained: the norm bound
   comes from Lemma 1.1 with `N = B(H)`. It is recorded as the claim
   `stw01-three-projection-corner-pair-is-universal-pair`, with the `requires: []` route
   `stw01-three-projection-corner-pair-is-universal-pair-proof`.
3. **Theorem 1 (corner-pair test).** Problem I holds iff every bounded 2-quasitrace on `P_3`
   satisfies `sigma(h_2 + h_3) = sigma(h_2) + sigma(h_3)`.
   - The inputs are the reviewed (I1)–(I4) and (I6): Gow Theorem A, Theorem 2.22, Corollary 3.10,
     and Blackadar–Handelman Corollary II.1.10 as quoted by Gow.
   - (I5), density of finite-spectrum elements, is dropped. No `g` and no scalar remain.
   - It is recorded as the claim `stw01-three-projection-corner-pair-quasitrace-additivity`, with
     the route `stw01-three-projection-via-corner-pair-additivity` into the target.
4. **Theorem 2 (normalized witnesses).** If Problem I fails, then for each sign there is a
   bounded 2-quasitrace `sigma` on `P_3` with:
   - `sigma(1) = 1`, `sigma(r_i) = 1/2` and `sigma(r_i r_j r_i) = 1/4`, the values of `tau_e`;
   - `sigma o alpha = sigma`;
   - `epsilon D_sigma(h_2, h_3) > 0`.

   The proof has four ingredients.
   - An affine rescaling `a = (1/2 - eta tau(x)) 1 + eta x` with `eta = 1/32`, so `tau(a) = 1/2`.
   - An intermediate-value tuning of the phase `theta`. The estimates are
     `f(0) >= 47/64 > 1/2 > 1/64 >= f(pi)` for `f(theta) = tau(w_theta^* w_theta)`, so
     `sigma(r_2 r_3 r_2) = 1/4`.
   - Halving the pulled-back quasitrace, and averaging with `alpha`.
   - Lemma 4.1: `beta` reverses the defect, because `beta(h_j) = r_1 - h_j`, and it preserves all
     the normalizations.

   This resolves the target's "equal trace" attempt: all three projections can have half trace.
5. **Corollary 4.2.** Each one-sided inequality `sigma(h_2 + h_3) <= (>=) sigma(h_2) + sigma(h_3)`,
   restricted to normalized quasitraces, is already equivalent to Problem I.
6. **Numerical sanity check.**
   `experiments/stw01-three-projection-corner-pair-2026-09-16/check_corner_dilation.py`, output in
   `output.txt` next to it. It covers the Lemma 1.1 identities, the `beta`-word trace identity, and
   the Step B constants, on random `6 x 6` matrices with the normalized trace. Errors are
   `< 2e-14`, all bounds hold, and the observed `f(0) >= 0.9997` and `f(pi) <= 3.2e-4`. Because it
   uses a trace, it checks algebra and constants only.

## Approaches tried and where each dies

- **Exactness of any host.** Every subalgebra containing `h_2, h_3` contains `V`, and `V` surjects
  onto `C^3 * C^2`, which is not exact (inherited). Dead.
- **Linearity on `C*(r_1, r_j)` (Haagerup on nuclear two-projection algebras).** It gives
  linearity on `C*(h_2)` and on `C*(h_3)` separately. Dead: nothing relates the two.
- **Proving just one inequality.** Dead: Corollary 4.2 makes each inequality equivalent to
  Problem I.
- **Elementary bounds.** Monotonicity, and the matrix sign flip `D_(sigma_2)(X, W X W) = -2 D_sigma(a, b)`
  for `X = z z^*`, `W = diag(1, -1)`. They give `sigma(h_2 + h_3) in [1/4, 1]`. Dead.
- **Pinching.** `D_sigma(h_2, h_3) = -(1/2) D_(sigma_2)(Y Y^*, W Y Y^* W)` for `Y = [(r_2 r_1, r_3 r_1)^T | 0]`.
  Dead: a restatement.
- **Averaging.**
  - `alpha` keeps the defect, so it only gives swap-invariance.
  - `beta` kills it, so a counterexample is never `beta`-invariant, and nothing forces invariance.
  - `S_3` mixes three different corner pairs, which can cancel.
- **Free-triple normalization (arcsine law of `h_2`).** Not reached: it needs nonlinear `g`, which
  breaks `D_tau(g(x), g(y)) = const * D_tau(x, y)`.
- **Order-pair (commuting sandwich) methods.** Dead: `h_2, h_3` satisfy no order relation
  (Proposition 3).
- **Complement trick** `D(x + beta q, beta(1 - q)) = -D(x, beta q)`. It was superseded by the
  automorphism `beta`, which realises the same sign flip inside `P_3`.
- **`K_0` / projections.** Granting `K_0(P_3) = Z^4` (Cuntz free-product formula, unverified) and the
  BH extension to `M_n`, a normalized witness matches `tau_e` on all projections over `P_3`. Stalls:
  `P_3` is not real rank zero, so no passage from projections to `h_2 + h_3` is known.
- **RFD (Exel–Loring, unverified).** Dead: non-linear quasitraces are not weak* limits of
  finite-dimensional traces.
- **`P_3 = C*(F_2) x| Z_2`** (index-two free subgroup `<s_1 s_2, s_1 s_3>`). Dead as a transfer:
  `h_j` have odd group components, and no extension of quasitraces from `P_3` to `M_2(C*(F_2))` is
  known.
- **Half-trace variant `sigma(r_1 r_2 r_1 + s r_3)` with a scalar `s`.** Abandoned early. The corner
  pair removes the scalar with no tuning.

**Honest assessment.** The pair `(h_2, h_3)` is as free as possible (`V`). The only content beyond
the trivial "Problem I iff additivity on `V` for all quasitraces on `V`" is that quasitraces
extending to `P_3` suffice, with a normalization. No mechanism forcing additivity was found.

## Alternative trust path (recorded, not used)

Suppose one grants the Blackadar–Handelman result that a 2-quasitrace extends to every `M_n(A)`
(primary not fetched, unverified). Then Theorem 1 (2) ⟹ (1) needs no AW*-factor. Dilate a
non-additive pair of any unital `A` into `M_2(A)`, and pull back the extension to `P_3`.

## Literature consulted (gate run 2026-09-16, arXiv export API over https, newest first)

- **Queries.** `all:quasitrace` and `all:quasitraces` (31 results each), and `abs:"AW*-factor"` (12).
- **arXiv:2601.04431v2**, A. Gow, "On the Quasitrace Problem and a Characterization of W*-algebras".
  Submitted 2026-01-07, v2 2026-07-14. Source of (I1), (I2), (I4), and of the BH quotation (I3).
  The abstract frames Problem I as open.
- **arXiv:2501.13088v2**, A. Gow, "Every 2-quasitrace is a trace", 2025-01-22 / 2025-01-31.
  Withdrawn. The comment reports a critical gap in Proposition 5.2, which breaks Theorem A
  (Corollary 5.3). It is replaced by 2601.04431.
- **arXiv:2609.10218v1**, J. Arulseelan and J. E. Hanson, "Every AW*-Algebra is Normal",
  2026-09-09. Normality was already known for AW*-factors (Saitô–Wright, per the abstract), so it
  does not decide monotone completeness of `II_1` AW*-factors, and Problem I stays open. The
  repo's assessment is in `research/artifacts/stw01-awstar-normality-assessment-2026-09-12.md`.
- **arXiv:2309.17412v2**, H. O. Milhøj and M. Rørdam, "Around traces and quasitraces"
  (2023-11-30). Survey abstract only; nothing on free products of projections.
- **Irrelevant hits.** arXiv:2607.20593v1 (Jiang–Ma–Shi–Zhang, Kaplansky's *second test problem*
  on similarity, 2026-07-22), arXiv:2512.23911v1 (Fu, 2025-12-30), arXiv:1403.7653v1 (Haagerup,
  "Quasitraces on exact C*-algebras are traces", only as the known exact case).
- **Not fetched, unverified here.**
  - Blackadar–Handelman 1982: Corollary II.1.10 on AW*-factors, and the general `M_n` extension.
  - Wright, on AW*-factors.
  - Cuntz, K-theory of free products.
  - Exel–Loring, RFD free products.

  None is used beyond Gow's quotations. The non-exactness of `C^3 * C^2` is inherited from
  `stw01-modular-test-pair-generates-non-exact-algebra` and not re-verified.

## Files

- `research/artifacts/stw01-three-projection-corner-pair-test-2026-09-16.md`
- `research/stw01-three-projection-corner-pair-quasitrace-additivity.md` (claim)
- `research/stw01-three-projection-via-corner-pair-additivity.md` (route into the target)
- `research/stw01-three-projection-corner-pair-is-universal-pair.md` (claim)
- `research/stw01-three-projection-corner-pair-is-universal-pair-proof.md` (route, `requires: []`)
- `experiments/stw01-three-projection-corner-pair-2026-09-16/check_corner_dilation.py`, `output.txt`

## Referee (2026-09-16)

Adversarial referee and landing pass on this lane's files.

**Checked by hand, line by line.**
- Lemma 1.1: projection identities, the `(1,1)` compressions, the partial isometries `W_a`,
  and `Z Z^* = P_2 P_3(theta) P_2`, `Z^* Z = w_theta^* w_theta (+) 0`.
- Proposition 3: existence of `psi` into the corner with unit `r_1`, the norm bound from the
  `B(H)` dilation (constant terms go to `1 (+) 0`), and isometry on the dense *-subalgebra.
  The `requires: []` route is complete; it uses only universal properties and functional
  calculus.
- Theorem 1: Step 0 and Step 2 are exactly the reviewed Steps 0 and 5 of
  `research/artifacts/stw01-three-projection-universal-test-2026-09-12.md`; the check
  `tau~(z (+) 0) = tau_4(z (x) e_11) = tau(z)` and the pullback along the surjection onto `B`
  are correct. Dropping (I5) is legitimate: the dilation takes the defect pair directly.
- Lemma 4.1: `beta(h_j) = r_1 - h_j`, commutativity of `C*(r_1, h_j)` and `C*(r_1, h_2 + h_3)`,
  the sign reversal, and all normalizations for `sigma o beta`, including the reversed words via
  (E1) with `w = r_1 (1 - r_j)` and the word `(1 - r_2)(1 - r_3)(1 - r_2)`.
- Theorem 2: spectra of the affine rescalings, `tau(a) = 1/2`, `D_tau(a, b) = eta D_tau(x, y)`,
  the Step B bounds (`|t^(1/2) - 2^(-1/2)| <= eta`, `||w_0 - 1||, ||w_pi|| <= 4 eta`,
  `||w_0^* w_0 - 1|| <= 17/64`, `f(pi) <= 16 eta^2`), `sigma_0(1) = 1` via the swap unitary,
  the half-trace values, `f(theta_0)/2 = 1/4`, symmetrization with `alpha`, and
  `alpha beta = beta alpha`.
- Remarks: the elementary bounds `[1/4, 1]`, the pinching identity
  `D_sigma = -(1/2) D_(sigma_2)(X, W X W)`, the expansion of `8 h_2`, the index-two free subgroup,
  and the complement-trick identity.

**Recomputed.** Reran `check_corner_dilation.py` single-threaded; output is byte-identical to
`output.txt`.

**Literature gate.** Fetched 2026-09-16: arXiv:2601.04431v2 (Gow, v1 2026-01-07, v2
2026-07-14; frames the 2-quasitrace question as open); arXiv:2609.10218 (Arulseelan–Hanson,
2026-09-09; normality of AW*-algebras, already known for factors); arXiv API newest-first
`all:quasitrace` shows no newer resolution. Problem I remains open. Blackadar–Handelman,
Cuntz, Exel–Loring and Wright remain unverified at the source, as the files already say.

**Duplicates.** `bin/cairn search --similar` on both new claims finds no duplicate;
`distinct_from` entries are accurate.

**Changed.** One wording fix in `stw01-three-projection-corner-pair-quasitrace-additivity`: the
two directions of the equivalence were labelled ambiguously ("converse"/"forward"), and the
external trust surface of the nontrivial direction is now named on the claim.

**Verdict.** Sound and honestly labelled. Proposition 3 is a complete direct proof. Theorems 1
and 2 and Corollary 4.2 are correct reductions resting on the same inherited external inputs as
the reviewed three-projection universal test. Nothing about Problem I or the target is settled.
Landed with the minor fix.
