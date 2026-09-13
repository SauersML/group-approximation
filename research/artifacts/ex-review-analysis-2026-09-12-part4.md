# EX review, analysis lanes, part 4: Rank Problem and Toms--Winter reductions (2026-09-13)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0. Main tip at
review time: `5cc8cb507`.

Neither famous root flipped. `stw23-rank-problem-counterexample-exists` is OPEN: its new route
`stw23-counterexample-from-toms-schubert-algebra` requires the OPEN `toms-schubert-algebra-misses-a-rank`.
`stw18-strict-comparison-non-z-stable-algebra-exists` is also OPEN.

## 1.9 ex-rank-problem-villadsen and ex-rank-problem-lix: Toms's no-Gamma algebra

### `all-ranks-occur-iff-continuous-ranks-are-dense` (814a8a6eb5, ddf8f06131): PASS

Re-derived.
- **Orthogonal sums.** `a = Σ 2^{-k}(1+||a_k||)^{-1} a_k ⊗ e_kk` has `d = Σ d(a_k)`, by sup-continuity.
- **(3 ⇒ 2), greedy residuals.** Approximate `r_k − m_k/2` within `m_k/4`. This gives
  `m_k/4 < r_{k+1} < 3m_k/4`, so `M_{k+1} < (3/4)M_k`.
- **(2 ⇒ 1), Edwards increments.** h_1 = g_N − m/4 and
  h_{k+1} = (g_{N+k} − g_{N+k−1}) + m(4^{-k} − 4^{-(k+1)}). They are strictly positive and continuous,
  with partial sums g_{N+k} − m·4^{-(k+1)} increasing to f.
- **Summands of a continuous rank.** A continuous finite function minus a lower semicontinuous one is
  upper semicontinuous.
- **Trust surfaces.** Blackadar--Handelman §II.4 and Edwards's separation theorem.

### `doubling-ah-finite-stage-continuous-ranks-are-constant` (814a8a6eb5): PASS

Re-derived.
- **Branch traces.** The diagonal sections give ψ_K(δ_{y_{K+1}}) = α_K δ_{y_K} + (1−α_K)ν_K.
  Σ(1−α) < ∞ gives total-variation convergence to β_L δ_{y_L} + κ_L, with κ_L independent of y.
- **Continuity.** y ↦ σ_y is weak* continuous.
- **Finite stage.** d_{σ_y}(a) = β_M R(y)/r_M + c, so a continuous rank forces the lower
  semicontinuous integer-valued R to be continuous, hence constant on connected X_M.
- **Orthogonal sums.** Use the summand lemma.
- **Instance check.** That Toms's systems satisfy the setting (connected spectra, a common diagonal,
  constant contamination) is read from arXiv:2606.12188v2 by the lane. I did not re-read it.

### `rank-density-and-small-joins-give-all-ranks` (a57ae731c8, 5eb6bccb86): PASS

Re-derived.
- **α(f) exists and d(α(f)) ≤ f.** L'_f is downward closed and directed, and its countable basis part
  has a cofinal chain.
- **d(α(f)) ≥ f.** (RD) gives a_n with g_n − ε_n ≤ d(a_n) ≤ g_n − ε_n/2. The test (C3) puts d(a_n) way
  below f, and every a'' ≪ a_n lies in L'_f.
- **Corollary (strict comparison with RD gives SJ).** Take c' = [(c_0 − 1/k)_+] with
  d(c') > h + ε/4 > d(a_1). Strict comparison gives a' ≤ [a_1] ≤ c'.
- **Trust surface.** Thiel arXiv:1711.04721: countably based dcpo, and the way-below relation in
  LAff(K).

### `toms-schubert-algebra-has-no-small-joins` (ddf8f06131, a53d522a03): PASS, conditional on the Toms imports

Re-derived.
1. **Reduce to one finite stage.** Compactness of [p_m] and Rørdam's lemma, at a finite stage n.
2. **Orthogonal copies.** Rescale to v, w with v*v = p_n and w*w = q_n, hereditary under b''. At a
   degeneracy point x_0 of the bundle map w*v, the two range projections are orthogonal inside
   ran b''(x_0), so rank b''(x_0) ≥ 2d_n.
3. **Branch trace.** It gives d_σ(c) ≥ 2β_n d_n/rank(s_n) = 2t_m ∏_{r≥m} α_r.

- **Trust surfaces.** (T1) total degeneracy and (T2), from arXiv:2606.12188. (Br) is the branch-trace
  construction verified above.
- **Corollary.** The failure of Thiel's Step 4 is correct. The disjunction "(O6+) fails or weak
  cancellation fails" is resolved by the next claim.

### `toms-schubert-algebra-fails-o6-plus` (16cd5f1cc8, 464531f0c9): PASS, conditional on the Toms and Thiel imports

Re-derived.
- **Near projections.** A support gap G < δ²/8 gives near projections z_P ≤ p_m and z_Q ≤ q̂_m, each
  with 2-norm defect ≤ G/k.
- **Approximate equivalence.** b = y'*x' has b*b = z_P² and bb* = z_Q², since x'x'* = y'y'* = h_ε(c).
  So ||p_m − b*b||_{2,u} < δ/(2√k) − s for some s > 0.
- **Contradiction.** Compressing at a late stage adds 2||b − b_n|| + √η_m ≤ 2||b − b_n|| + δ/(2√k).
  Choosing ||b − b_n|| < s/2 keeps the total strictly below δ/√k. Total degeneracy and the atom trace
  τ_x force ≥ δ/√k.
- **Corollaries.** Thiel's Theorem 7.5 would attain d(c) = d(p_m), against Corollary B, so (O6+)
  fails. Theorem 6.4 and Remark 6.5 then give that almost stable rank one fails.

### `o6-plus-forces-tracial-equivalence-of-equal-trace-projections` (6bf99b8316, 203674d9b1): PASS

Re-derived.
- Thiel's Theorem 7.5 gives c ≾ p, q with d(c) = d(p).
- Dini's theorem makes the support gaps tend to 0.
- The same rescaling gives ||p − b*b||²_{2,u} ≤ 2G_ε/k.
- The comparison version uses only z_P → p and vv* ≤ q.
- The C(S²) non-simple illustration and Thiel's Example 6.7 were not re-read. They are labelled as
  illustrations.

## 1.10 ex-toms-winter: divisibility of the unit on Bauer simplices

### `bauer-tracially-divisible-unit-gives-bounded-rank-density` (eca20c7e2a): PASS

Re-derived from §1 of `ex-toms-winter-bauer-divisible-unit-2026-09-12.md`.
- **Transition count.** For i with φ_i(λ) > 0, the r_i/N lie within η/4 + 1/N of f(λ). So fewer than
  Nη/2 + 1 of the ψ_j are strictly between 0 and 1 at λ.
- **Defect bound.** ≤ (1/4N)(Nη/2 + 1) + η/8 < η/3.
- **Profile.** Within η/2.
- **Pull back.** e_j^{1/2} z_j e_j^{1/2} = z_j e_j, so ||b − B||_{2,λ} < η/12. The bounds pass to all
  traces by integrating against the representing measures.
- **Trust surface.** Ozawa arXiv:1304.3523, Theorem 3 and A^u = A^st. This is the only place the Bauer
  hypothesis is used.

### `strict-comparison-unit-divisibility-equivalences` (aa6b4d74d4): PASS

- **2 ⇒ 3.** Rank bounds plus strict comparison.
- **4 ⇒ 3.** An integer m ∈ [(L+1)/(n+1), L/n] exists once L ≥ n(n+1) + n. Then nmx ≤ Lx ≤ [1] and
  [1] ≤ (L+1)x ≤ (n+1)mx.
- **3 ⇒ 5.**
  - e_j ~ (d − δ/2)_+ gives d_τ((e_j − δ/2)_+) = d_τ((d − δ)_+) > 1/(n+1).
  - So d_τ(1 − Σ b_j) < d_τ((b_1 − ε')_+), strict comparison gives Rørdam--Winter (ii), and (iv)
    follows.
  - Rørdam--Winter arXiv:0801.2259 Proposition 5.1 is quoted verbatim, including its remark that
    stable rank one is used only in (i) ⇒ (ii).
- **6 ⇒ 1** uses Lemma 3.2 of the part 2 artifact, the order zero map `M_N → Z_{n,n+1}`. I did not
  re-read that lemma.

### `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit` (eca20c7e2a, aa6b4d74d4): PASS

- Every prerequisite of `toms-winter-bauer-tlfnd-divisible-unit-proof` has a `requires: []` route. These
  include the ultrapower comparison, division, support projection and uniform Gamma nodes, earlier
  reviewed PASS in `review-toms-winter-ultrapower-comparison-2026-09-12` and
  `review-swarm6-analysis-2026-09-12`.
- **(a) ⇒ (d).** Z has tracially large order zero maps, transported through A ⊗ Z ≅ A.
- **Counterexample shape.** The clauses are negations of (d), (e) and (f).
- The claim title and body keep the stated hypotheses (Bauer, tlfnd, strict comparison), and nothing
  is claimed unconditionally.

### `bauer-strict-comparison-pure-iff-divisible-unit` (39971c4c98): PASS

- **(c ⇒ b).** For t ∈ [0,1], |1_{(1/2,1]}(t) − t| ≤ 2t(1−t), so
  |d_τ((q − 1/2)_+) − τ(q)| ≤ 2τ(q − q²).
- **(b ⇒ a).** `rank-density-and-strict-comparison-give-purity`.
- **(a ⇒ d).** Almost divisibility at the compact class [1], with a W(A) approximant.
- Rørdam--Winter (iv) ⟹ (i) is flagged as not re-read, and it enters only a counterexample clause.
