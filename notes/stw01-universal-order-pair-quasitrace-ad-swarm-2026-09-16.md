# STW Problem I on the universal order pair: swarm lane, 2026-09-16

Lane `swarm-stw01-universal-order-pair-qua`. Locked hole:
`stw01-universal-order-pair-quasitrace-additivity`. Outcome: **obstruction**.

- Symmetrization over the Klein four-group `K` of automorphisms of `U` is dead.
- No element of `K` can play the defect-reversing role that an automorphism plays in the
  three-projection lane.
- Automorphisms of `U` outside `K` exist and were not analysed.
- Nothing new is settled about Problem I.

## Setup

- **Target.** `U` is the universal unital C*-algebra of `0 <= h_0 <= 1`,
  `0 <= k_0 <= c_0 := h_0 - h_0^2`. The target says every bounded 2-quasitrace `sigma` on `U` has
  `D_sigma(h_0, k_0) := sigma(h_0 + k_0) - sigma(h_0) - sigma(k_0) = 0`.
  - It is equivalent to STW Problem I (Kaplansky's quasitrace problem), by Theorem B of
    `research/artifacts/stw01-universal-order-pair-test-2026-09-12.md`.
  - Its reverse direction is the direct route `stw01-problem-i-via-universal-order-pair`, through
    the affine rescaling `stw01-order-pair-defects-rescale-generic-defects`.
- **Status gate (2026-09-16).** Problem I is open.
  - The newest relevant arXiv item, 2601.04431v2 (Gow, v2 2026-07-14), frames it as open.
  - Gow's claimed solution 2501.13088 is withdrawn.
  - The 2026-09-09 normality paper 2609.10218 does not settle it, per the repo assessment
    `research/artifacts/stw01-awstar-normality-assessment-2026-09-12.md`.
  - Details are under "Literature consulted".
- **Recorded attempts, before this lane.** Commuting sandwich, ideal extension, Cuntz semigroup,
  free products and pinching, spectral localization, free-product model and RFD, norm-local exact
  approximation, non-additive dimension functions.
- **What this lane tried.** The sibling three-projection lane
  (`notes/stw01-three-projection-algebra-quasitrac-swarm-2026-09-16.md`) found an automorphism of
  `P_3` that reverses its corner-pair defect for every quasitrace. So its witnesses can never be
  invariant under that automorphism. The question here was whether `U` has a symmetry with the
  same effect, which would give a contradiction from a symmetric witness.
- **Axioms used.** Only these properties of a bounded 2-quasitrace:
  - (F1) linearity on commutative C*-subalgebras, which gives translation covariance (T),
    oddness (O) and positive homogeneity (H) on `A_sa`;
  - (F2) monotonicity, quoted from Haagerup arXiv:1403.7653v1, Corollary 3.4(1), which in turn
    quotes Blackadar–Handelman (see "Weakest step" below);
  - (F3) the Lipschitz bound `|sigma(a) - sigma(b)| <= ||a - b|| sigma(1)`;
  - (F4) stability under pullback along unital *-homomorphisms and under nonnegative combinations.
- **Notation.**
  - `E_sigma(a, b) = sigma(b + a) + sigma(b - a) - 2 sigma(b) = D(a, b) + D(a - b, b)`;
  - `phi_(a,b)(t) = sigma(b + t a)`;
  - `Delta_rho` and `Delta2_rho` are the first and second differences of step `rho`.

## What was proven

Everything is in `research/artifacts/stw01-order-pair-klein-symmetrization-2026-09-16.md`, with
complete proofs. No new claim or route node was created: the results are obstructions and
reformulations, recorded as an Attempts bullet on the target.

1. **Lemma 2.1 (the Klein group).**
   - `beta : h_0 -> 1 - h_0, k_0 -> k_0` and `gamma : k_0 -> c_0 - k_0` are commuting involutive
     automorphisms of `U`, by universality, and together they generate a Klein four-group `K`.
   - Characters of `U` show the three nontrivial elements are distinct.
   - In `Q = C*(PSL_2(Z))`, `gamma` is the restriction of the swap `e_2 <-> e_3`.
2. **Lemma 2.2 (defect transformation).** `D_(rho o g)(h_0, k_0)` equals:
   - `D_rho(h_0 - k_0, k_0)` for `g = beta`;
   - `D_rho(h_0, c_0 - k_0)` for `g = gamma`;
   - `D_rho(h_0^2 + k_0, c_0 - k_0)` for `g = beta gamma`.

   Also `D_rho + D_(rho o beta) = E_rho(h_0, k_0)`. These use only (T) and (O).
3. **Lemma 3.1 (pulled-back Klein sum).**
   - Take `h = lambda + eps x` and `k = s + eps y`, with `x, y` self-adjoint contractions and
     either `(lambda, s, eps) = (1/4, 3/32, <= 1/20)` or `(1/2, 1/8, <= 1/10)`. Then
     `0 <= k <= h - h^2` (Lemma 1.1), which gives `pi : U -> A`.
   - `sum_(g in K) D_(tau o pi o g)(h_0, k_0) = eps [E_tau(x, y) + E_tau(x, w_eps)]`, with
     `w_eps = (1 - 2 lambda) x - y - eps x^2`.
4. **Remark 3.2 (the centre `1/2` is degenerate).**
   - `D_1 + D_beta = eps E(x, y)` exactly.
   - `D_1 + D_(beta gamma)` is `O(eps^2)`, because `D(x, y) + D(x + y, -y) = 0` by (O), and the
     Klein sum is also `O(eps^2)`.
   - So centring at `1/2`, the centre of the earlier rescaling artifact, hides the first-order
     information. The lane had to move to the centre `1/4`.
5. **Lemma 4.1 (line criterion).** A bounded 2-quasitrace is a trace iff every line
   `phi_(a,b)` is affine, iff `E >= 0` everywhere, iff `E <= 0` everywhere. Midpoint convexity plus
   (F3)-continuity gives convexity. Oddness gives concavity of the reflected line. The slope is
   read off at infinity with (H) and (F3).
6. **Lemma 4.2 (periodic differences).** Let `f` be continuous on `R` with bounded differences.
   - (i) If `Delta_rho f` has period `kappa rho` for every `rho > 0`, then `f` is affine. Summing
     `n` steps gives period `kappa rho / n`; the closed period group is `R`; so `Delta_rho f` is a
     continuous additive `c(rho)`.
   - (ii) `Delta2_rho f(t) = Delta2_rho f(t - nu rho)` implies the hypothesis of (i) with
     `kappa = nu`. Put `chi = Delta_(nu rho) f`: it has zero second differences on each coset
     `t + rho Z` and is bounded, so it has period `rho`.
7. **Theorem 5.1 (Klein-invariant witnesses).** Problem I is equivalent to:
   - additivity on `(h_0, k_0)` for `K`-invariant bounded 2-quasitraces on `U` only;
   - even to the one-sided inequality `D <= 0` for them, or to `D >= 0`.

   So if Problem I fails, `U` carries `K`-invariant witnesses of each sign.

   *Proof shape.*
   - Average `tau o pi` over `K` at the centre `1/4`.
   - Let `eps -> 0` using (1.4): `E(x, y) + E(x, x/2 - y) <= 0`.
   - Apply the inequality to `(-x, -y)` for equality, and use homogeneity.
   - Rewrite the equality as `Delta2_1 phi(0) = Delta2_1 phi(-1/2)`.
   - Rescale the line to `(rho x, y + t_0 x)` to get (4.2.1) with `nu = 1/2`.
   - Apply Lemma 4.2 and Lemma 4.1.
8. **Proposition 6.1 (no unconditional reversal).** For each `g != 1` in `K`, the statement
   "`D_(sigma o g) + D_sigma <= 0` for all `sigma`" (or `>= 0`, or `= 0`) is equivalent to Problem I.
   - `beta`: `E(x, y) = 0` at either centre.
   - `gamma` at the centre `1/2`: `D(x, y) + D(x, -y) = E(y, x) = 0`.
   - `beta gamma` at the centre `1/4`: `D(x, y) + D(x/2 + y, x/2 - y)` equals
     `Delta_(1/2) phi(1/2) - Delta_(1/2) phi(-1/2)`. Its vanishing for all rescaled lines makes
     `Delta_q phi` `2q`-periodic, and Lemma 4.2(i) applies.

   So the `P_3` mechanism, a symmetry reversing the defect for every quasitrace, cannot exist
   inside `K` unless Problem I is already true. The corollary also records that, for each subgroup
   `H` of `K`, a proof may assume `H`-invariance and a counterexample search may prescribe the sign.
9. **Numerical sanity check.**
   `experiments/stw01-order-pair-klein-symmetrization-2026-09-16/check_klein_defects.py`, with
   output in `output.txt` (exit 0).
   - It uses 200 random `6 x 6` Hermitian contraction pairs and two nonlinear test functionals
     satisfying (T), (O), (H). They are deliberately not quasitraces, so the identities are tested
     nontrivially.
   - Maximum error over all algebraic identities is `9.8e-15`. The order-relation margin is
     `2.3e-2` at `lambda = 1/4`, `eps = 1/20`.
   - The `O(eps^2)` ratio at the centre `1/2` is `0.360`, `0.321`, `0.317`.
   - It checks algebra only, not the analytic lemmas or the limits.

## Approaches tried and where each dies

1. **Symmetrization over `K`.**
   - *Idea.* Average a witness over `beta`, `gamma`, `beta gamma` and hope the defect cancels.
     At the centre `1/2` the averaged defect is `O(eps^2)`, which looks promising.
   - *Where it dies.* Remark 3.2 shows the cancellation is an artefact of the centre `1/2`. At the
     centre `1/4`, Theorem 5.1 shows `K`-invariance costs nothing: invariant witnesses of either
     sign exist iff Problem I fails.
2. **Unconditional defect reversal (the `P_3` mechanism).**
   - *Idea.* Find `g` with `D_(sigma o g) = -D_sigma` for all `sigma`, as the complement flip does
     in `P_3`. A `g`-invariant witness would then be impossible, and averaging would kill every
     witness.
   - *Where it dies.* Proposition 6.1: for every `g != 1` in `K`, the reversal, and even its
     one-sided version, is already Problem I.
   - The reason is structural. In `P_3` the flip replaces each corner element by its complement
     inside a commutative corner, and `D(1 - a, 1 - b) = -D(a, b)` follows from (T) and (O). On `U`
     each nontrivial `g` produces a genuinely different pair (Lemma 2.2), which is tied to the
     original only through differences along lines.
3. **Affine self-similar endomorphisms.**
   - *Idea.* Endomorphisms `psi` of `U` of the form `h_0 -> alpha + t h_0`, `k_0 -> s_0 + t k_0`
     (`t > 0`, real constants `alpha`, `s_0`) satisfy `D_(sigma o psi)(h_0, k_0) = t D_sigma(h_0, k_0)`
     by (1.1). Also `(sigma o psi)(1) = sigma(1)`.
   - So an endomorphism with `t > 1` would push `sup |D_sigma(h_0, k_0)|` over normalized
     quasitraces (a finite number, by (F3)) past itself, forcing it to be `0`.
   - *Example.* `h_0 -> 1/2 + eps (2 h_0 - 1)`, `k_0 -> 1/8 + eps (2 k_0 - 1/4)` preserves the
     relations for `0 < eps <= 1/4`. The bounds are `k >= 1/16` and
     `1/8 + eps/4 <= 1/4 - eps^2 <= h - h^2`. So `t = 2 eps <= 1/2`.
   - *Where it dies.* In general `t <= 1`, because `sp(h_0) = [0, 1]` (the characters
     `h_0 -> lambda, k_0 -> 0`) and `alpha + t [0, 1]` must lie in `[0, 1]`. And `t = 1` forces
     `alpha = 0`, and then `s_0 = 0`, from `0 <= s_0 + k_0 <= h_0 - h_0^2` at the character
     `(h_0, k_0) -> (0, 0)`. So such endomorphisms only shrink defects, and yield nothing beyond
     the trivial `sup |D| >= t sup |D|`.
4. **One-sided inequalities.**
   - *Idea.* Prove `D <= 0` (or `>= 0`), or `E >= 0`, for all quasitraces on `U`.
   - *Where it dies.* By Lemma 4.1 and Proposition 4.1 of
     `research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md`, a
     quasitrace satisfying any one-sided inequality everywhere is a trace. By Theorem 5.1, the
     inequality on the single pair `(h_0, k_0)`, even restricted to `K`-invariant `sigma`, is
     already Problem I. No asymmetry is available to exploit.
5. **Finite-spectrum quotients of `U`.**
   - *Both `h_0` and `k_0` with two-point spectrum.* Then `C*(1, h_0, k_0)` is generated by two
     projections. It is a quotient of `C^2 * C^2 = C*(Z_2 * Z_2)`, and `Z_2 * Z_2` is the infinite
     dihedral group, which is amenable. So the quotient is nuclear, and every bounded
     2-quasitrace on it is a trace (Haagerup's exact case). No witness lives there.
   - *`h_0` with spectrum `{1/2 - delta, 1/2 + delta}`, `k_0` general.*
     - Then `h_0 - h_0^2 = (1/4 - delta^2) 1`, so this quotient is the universal algebra of a
       projection `p` and a positive `k <= 1/4 - delta^2`. That is `C^2 * C([0, 1])`, which
       surjects onto `Q` and is not exact.
     - Write `h_0 = (1/2 - delta) + 2 delta p`. By (T) and (H),
       `D(h_0, k) = 2 delta D(p, k/(2 delta))`, and by (T) `D(p, w + r 1) = D(p, w)` for real `r`.
     - Given a projection `p` and a self-adjoint `w` in any unital algebra, shift `w` to be
       positive. Then take `delta` so small that `2 delta ||w + r|| <= 1/4 - delta^2`, and put
       `k = 2 delta (w + r)`. This is an order pair, so additivity on `U` gives `D(p, w) = 0`.
       So this quotient tests `D(p, w) = 0` for every projection `p` and every bounded
       self-adjoint `w`, in every unital algebra.
     - On a real rank zero algebra, that already gives linearity. Approximate `a` by
       `sum lambda_i p_i`, peel off one projection at a time using (H) and (O), and finish with
       (F3).
     - Combined with the reduction of Problem I to `II_1` AW*-factors (Gow, Theorem A, as quoted
       in the sibling lane and not re-verified here; AW*-algebras have real rank zero), projection
       additivity is again all of Problem I.
     - *Where it dies.* This quotient loses nothing, so there is no simplification.
6. **The pinching algebra `B = C*(1, e_2, g)` with `g = p e_1 p` (revisited).**
   - *Idea.* `Z = [[p e_1, 0], [e_2 p e_1, 0]]` gives `Z^* Z = (h + k) (+) 0` and
     `Z Z^* = X = [[g, g e_2], [e_2 g, e_2 g e_2]]` in `M_2(B)`. The pinching is
     `E_2(X) = (X + D X D)/2` with `D = diag(1, -1)`, and `sigma_2(E_2(X)) = sigma(h) + sigma(k)`.
   - So if `B` were exact, Haagerup's theorem would make `sigma_2` linear on `M_2(B)`. This needs
     `sigma_2|M_2(B)` to be a 2-quasitrace, which is the Blackadar–Handelman `2 => n` extension
     quoted in 1403.7653 (introduction and Corollary 3.4(2)).
   - Linearity plus unitary invariance would give `sigma_2(X) = sigma_2(E_2(X))`, and
     `sigma_2(X) = sigma_2(Z Z^*) = sigma_2(Z^* Z) = sigma(h + k)`. That is the modular test on `Q`,
     hence Problem I (`stw01-problem-i-via-modular-single-pair`).
   - *Where it dies.* Exactness of `B` was not decided, and this lane found no route to decide it.
     - `B` is a proper quotient of `C^2 * C([0, 1])`. The pair `(e_2, g)` satisfies nontrivial
       relations, for example `||e_2 g e_2|| = ||e_1 p e_2||^2 <= 1/4`, because
       `e_1 p e_2 = e_1 (p - 1/2) e_2`.
     - So the non-exactness of `C^2 * C([0, 1])` does not transfer.
     - The three-block dilation of Theorem A does not keep `e_2` block diagonal against `g`, so no
       universality statement for `(e_2, g)` was obtained either.
7. **Line asymptotics.**
   - *Idea.* Constrain `phi_(x,y)` at infinity and propagate back to `t = 1`.
   - *Where it dies.* (H) and (F2) give
     `lambda_min(y) sigma(1) <= phi(t) - t sigma(x) <= lambda_max(y) sigma(1)` for `t > 0`. At `t = 1`
     this is only the generic bound
     `lambda_min(y) sigma(1) - sigma(y) <= D(x, y) <= lambda_max(y) sigma(1) - sigma(y)`. It allows
     any bounded deviation from affinity. By Lemmas 4.1 and 4.2, what is needed instead is exact
     affinity along lines, or periodic differences, and that is Problem I again.
8. **Local Cuntz models.**
   - *Idea.* Compute `d((h_0 + k_0 - t)_+)` in finite-dimensional or commutative quotients of `U`.
   - *Where it dies.* These quotients are exact and see only traces. `U` is RFD, but pointwise
     limits of traces are traces (target, Attempts), so no local model reaches a quasitrace that is
     not a trace.
9. **Non-exactness as a symptom (side remark).**
   - *Idea.* Is non-exactness of `U` itself evidence for a counterexample?
   - *Where it dies.* No.
     - **The example.** `B = (K (x) C*(F_2))~` is not exact: it contains `C*(F_2)`, which is not
       exact (Wassermann, standard, not re-fetched).
     - **Why its quasitraces are traces.** Let `sigma` be a bounded 2-quasitrace on `B`, and `j`
       a positive element of the corner `P_n (K (x) C*(F_2)) P_n`, where
       `P_n = sum_(i <= n) e_ii (x) 1`. The partial isometries
       `v_m = sum_(i <= n) e_(i + mn, i) (x) 1` lie in `B`. The elements `v_m j v_m^*` with
       `0 <= m < M` are mutually orthogonal, and each has value `sigma(j)`, so `M sigma(j) <= ||j|| sigma(1)` by (F1), (F2) and (x^* x ~ x x^*).
       Hence `sigma` vanishes on the stable ideal by (F3), and by (T) `sigma` is `sigma(1)` times the
       character. So every bounded 2-quasitrace on `B` is a trace.
     - **A variant with a faithful trace.** Extend `(+) M_(k_n)` by `B` inside `prod M_(k_n)` and
       use `stw01-extensions-preserve-qt-linearity`. Its existence needs the Blackadar–Kirchberg MF
       embedding, which was not fetched.
     - This is not new: it follows immediately from repo results. It only shows that non-exactness
       of `U` carries no signal either way.

## Literature consulted

Gate run 2026-09-16 through the arXiv export API over https.

- **Query.** `all:quasitrace`, run at about 02:40 UTC, returned 31 results. The re-queries at about
  03:05 UTC and 03:25 UTC failed (HTTP "Rate exceeded", then proxy tunnel timeouts), so the newest
  data is from the 02:40 run.
- **arXiv:2601.04431v2.** A. Gow, "On the Quasitrace Problem and a Characterization of
  W*-algebras". v1 2026-01-07, v2 2026-07-14. This is the newest relevant hit. Its abstract
  frames Problem I as open, and it is the source of the Gow AW*-factor reduction quoted in the
  sibling lane.
- **arXiv:2501.13088v2.** A. Gow, "Every 2-quasitrace is a trace", 2025-01-22 / 2025-01-31.
  Withdrawn.
- **arXiv:2309.17412v2.** H. O. Milhøj and M. Rørdam, "Around traces and quasitraces"
  (2023-11-30). Survey; abstract only.
- **arXiv:1403.7653v1.** U. Haagerup, "Quasitraces on exact C*-algebras are traces" (C. R.
  Math. Rep. Acad. Sci. Canada 36 (2014), 67–92). Text extracted 2026-09-16. Three parts were used:
  - the introduction: the exact case, and the quotation of the Blackadar–Handelman `2 => n`
    extension;
  - Definition 3.1, where "quasitrace" means a 2-quasitrace;
  - Corollary 3.4, which quotes Blackadar–Handelman Section II. Part (1), order preservation on
    `A_sa`, is the source for (F2). Part (2) gives the `M_n` extension.
- **arXiv:2609.10218v1.** J. Arulseelan and J. E. Hanson, "Every AW*-Algebra is Normal",
  2026-09-09. Taken from the sibling lane's gate and the repo assessment
  `research/artifacts/stw01-awstar-normality-assessment-2026-09-12.md`; it was not fetched here.
  It does not settle Problem I.
- **Other hits in the 31.** 2512.23911v1, 2505.22448v1, 2406.11052v3, 2303.01929v2 and older.
  None addresses automorphism-symmetrization of quasitraces or the order-pair algebra.
- **Repo sources.**
  - `research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md`: status,
    axioms (F2)–(F3), stable invisibility, and STW arXiv:2506.10902v2 as cited there.
  - `research/artifacts/stw01-universal-order-pair-test-2026-09-12.md` (Theorems A and B).
  - `research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md` (Proposition 4.1).
  - `notes/stw01-three-projection-algebra-quasitrac-swarm-2026-09-16.md` (the `P_3` flip).
- **Not fetched, unverified here.**
  - Blackadar–Handelman 1982 (monotonicity and the `2 => n` extension, used only as quoted).
  - Wassermann on the non-exactness of `C*(F_2)`.
  - Blackadar–Kirchberg on MF algebras.
  - That AW*-algebras have real rank zero (standard).

  None is used in the artifact's Sections 1–6 except (F2).

## Honest assessment

- **Status of the target.** Unchanged. It is open and equivalent to Problem I. Nothing here
  proves or refutes it, and nothing narrows the class of possible counterexamples beyond free
  normalizations.
- **What is solid.**
  - Lemmas 2.1, 2.2 and 3.1, and Remark 3.2, are exact algebraic identities using (T), (O) and
    (H) only. They are checked numerically on non-quasitrace test functionals.
  - Lemmas 4.1 and 4.2, Theorem 5.1 and Proposition 6.1 are short elementary arguments using
    (F1)–(F4). I re-derived every step by hand after writing it.
  - All of it is elementary. Lemma 4.1 is a per-quasitrace companion of Proposition 4.1 of the
    certificates artifact. I claim no novelty beyond this repository for the line lemmas.
- **What it is worth.**
  - It is an *obstruction* to two natural attacks: symmetrizing a witness over `K`, and importing
    into `K` the defect-reversing symmetry that works on `P_3`.
  - It gives two normalizations, usable by a proof or by a counterexample search:
    `K`-invariance, and a prescribed sign of the defect.
  - It warns that the centre `1/2` of the earlier rescaling hides first-order information under
    symmetrization.
  - These are reformulations of an open problem, not propositions about it. So they are recorded
    as an Attempts bullet on the target, with no new claim or route node.
- **Conditional side items.** Approaches 5, 6 and 9 rely on quotations not verified here: Gow's
  AW*-factor reduction, the Blackadar–Handelman `2 => n` extension, Wassermann, and
  Blackadar–Kirchberg. They are in these notes only, not in any node, and they carry no weight in
  the artifact.
- **Not attempted.**
  - The Cuntz classes of the cut-downs `(h_0 + k_0 - t)_+` in `U` itself.
  - Automorphisms of `U` outside `K`. Inner automorphisms are invisible to quasitraces, but there
    are others, found while writing these notes.
    - For a homeomorphism `f` of `[0, 1]` with `q_f = (f - f^2) / (lambda - lambda^2)` extending
      continuously and positively to `[0, 1]`, `psi_f : h_0 -> f(h_0)`,
      `k_0 -> g_f(h_0) k_0 g_f(h_0)` with `g_f = q_f^(1/2)` is an automorphism. The proof is in
      artifact Section 7.
    - The defect of `sigma o psi_f` is `D_sigma(f(h_0), g_f(h_0) k_0 g_f(h_0))`, which is not tied
      to the original defect by (T), (O) and (H).
    - Neither symmetrization nor reversal over these automorphisms was analysed.
  - Deciding whether the pinching algebra `B = C*(1, e_2, p e_1 p)` is exact.

### Weakest step

A referee should attack these first.

1. **(F2) monotonicity.**
   - It is quoted, not proved. The source is Haagerup arXiv:1403.7653v1, Corollary 3.4(1), which
     quotes Blackadar–Handelman 1982, Section II. Blackadar–Handelman was not fetched.
   - It enters only through (F3), and hence through (1.4) and (1.5): the limit `eps -> 0` in
     Theorem 5.1, Step 2; the continuity in Lemma 4.1; and the bounded differences in Lemma 4.2.
   - It is standard, and the repo audit uses the same axiom set.
2. **Lemma 4.2(ii).**
   - Its boundedness step turns the vanishing second differences of `chi = Delta_p f` on cosets
     `t + rho Z` into `rho`-periodicity.
   - It uses `sup |Delta_p f| < infinity`, which for line functions comes from (1.5).
3. **(F4).**
   - The claim is that `(1/4) sum_(g in K) tau o pi o g` is again a bounded 2-quasitrace.
   - Every axiom is preserved by pullback along unital *-homomorphisms and by convex combinations:
     the trace property `sigma_2(x^* x) = sigma_2(x x^*)` on `M_2`, linearity on commutative
     C*-subalgebras, positivity, and the `M_2` extension `tau_2 o ((pi o g) (x) id)`.

## Files

- **Created.**
  - `research/artifacts/stw01-order-pair-klein-symmetrization-2026-09-16.md`: the full proofs,
    Sections 1–9.
  - `experiments/stw01-order-pair-klein-symmetrization-2026-09-16/check_klein_defects.py` and
    `output.txt`: the algebraic sanity check.
  - `notes/stw01-universal-order-pair-quasitrace-ad-swarm-2026-09-16.md`: this file.
- **Modified.** `research/stw01-universal-order-pair-quasitrace-additivity.md`: added the new
  artifact to `artifacts:`, and appended the Attempts bullet "Symmetrization over the order-pair
  automorphisms", which includes the note that automorphisms outside `K` were not analysed.
- No claim or route node was created, and no commit was made.
