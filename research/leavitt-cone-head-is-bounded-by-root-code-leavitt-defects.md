---
rg: 2
id: leavitt-cone-head-is-bounded-by-root-code-leavitt-defects
kind: claim
title: In every unitary representation of the Leavitt cone cover, the head is at most the sum of long Leavitt defects over any codeword of the negative root code
distinct_from:
  leavitt-cone-head-bound-is-finite-congruence-gluing: that reduces (QC) to gluing finite Steinberg groups over finite cone quotients and reads the head on the edge group; this proves an explicit inequality bounding the head by long Leavitt relators of K, indexed by the linear dependences among the images of the words t_w in the finite quotient B_-.
  leavitt-cone-cover-hamming-head-bound-holds: that proves (QC) for permutation and monomial representations from nonsoficity of R^x; this holds for every unitary representation, gives no dimension-free bound by itself, and says which relators any dimension-free bound must control.
  leavitt-cone-head-bound-holds-for-all-ring-shadows: that bounds the head for representations induced from ring shadows, where every relator is an exact Steinberg relation; this is a relator inequality valid for arbitrary unitary representations of Gamma, in which Leavitt relators are only approximately trivial.
  atomic-leavitt-gap-on-nonzero-matrix-corner: that is an operator-norm gap for matrices satisfying the Leavitt relations approximately; this concerns group relators in the cone cover and bounds the head, not a ring defect.
artifacts:
  - research/leavitt-cone-head-root-code-bound-proof.md
  - experiments/leavitt-root-code-2026-09-17/root_code_census.py
  - experiments/leavitt-root-code-2026-09-17/census-output.txt
---

**ESTABLISHED** (route `leavitt-cone-head-root-code-bound-proof`; lane swarm-0917-w21-w21-nh-last1; unreviewed).

**Setting** (as in `leavitt-cone-head-bound-is-finite-congruence-gluing`).
- `R = L_(F_2)(1,2)`, `q = s_1 t_1`, `R_+ = <s_1,s_2,q>`, `R_- = <t_1,t_2,q>`, `R_0 = F_2 + F_2 q`.
- `Gamma = Delta_+ *_(Delta_0) Delta_-`, `Delta_+- = E_20(R_+-)`, `z = x_13(q)`.
- For a word `w = w_1...w_N` in `{1,2}^N`, put `s_w = s_(w_1)...s_(w_N) ∈ R_+` and
  `t_w = t_(w_N)...t_(w_1) ∈ R_-`. In `R`, `t_w s_(w') = δ_(w w')` for `|w| = |w'|`.
- Fix `c ∈ {1, q}` (so `c ∈ R_0`). The **long Leavitt relators** of depth `N` are

  ```text
  l^c_(w,w') = [x_12(t_w), x_23(s_(w') c)] · x_13(δ_(w w') c)^(-1)        (|w| = |w'| = N).
  ```

  Each lies in `Gamma` (the commutator entries are in `Delta_-` and `Delta_+`, and `x_13(δc)` is in `Delta_0`), and
  each lies in `K = ker(Gamma -> Delta)`.
- These relators carry the isometry relations `t_w s_w = 1` on the column `c`. The mixed relator
  `kappa = [x_12(s_1), x_23(t_1)] z^(-1)` carries `s_1 t_1 = q` instead.

**Theorem.** Let `rho : Gamma -> U(d)` be unitary, and let `I_- ⊆ R_-` be the congruence ideal of
`leavitt-cone-head-bound-is-finite-congruence-gluing` (1): `rho` kills `x_ij(I_-)`, and `[R_- : I_-] <= 2^d`.
Let `||.||` be any unitarily invariant norm (normalized Hilbert–Schmidt or operator norm).

1. **Root code.** For each `N`, the set of `S ⊆ {1,2}^N` with `sum_(w∈S) t_w ∈ I_-` is a binary linear code
   `C_N(rho)` of length `2^N` and codimension at most `k_- := log_2 [R_- : I_-] <= d`.
2. **Code bound.** For every nonzero `S ∈ C_N(rho)` and every `w_0 ∈ S`,

   ```text
   || rho(x_13(c)) - 1 ||  <=  sum_(w ∈ S) || rho(l^c_(w, w_0)) - 1 ||.                        (RC)
   ```

   Exactly one term is a diagonal defect (`w = w_0`). The rest are orthogonality defects.
3. **Approximate form.** If `S ⊆ {1,2}^N` is nonempty and `η = || rho(x_12(sum_(w∈S) t_w)) - 1 ||`, then

   ```text
   || rho(x_13(c)) - 1 ||  <=  2η + sum_(w ∈ S) || rho(l^c_(w, w_0)) - 1 ||.                   (RC_η)
   ```

   In normalized Hilbert–Schmidt norm, `η^2 = 4 μ{χ : χ(a) = 1}`, where `a = sum_S t_w`. Here `μ` is the spectral
   measure of `rho` restricted to the elementary abelian 2-group `x_12(R_-/I_-)`, and characters are identified with
   `F_2`-linear functionals `χ` on `R_-/I_-`. So `η`-codewords are the sums of small `μ`-weighted Hamming weight.
4. **Depth bounds.**
   - *Collision:* `C_N(rho)` contains a word of weight at most 2 once `2^N > 2^(k_-)`, i.e. at `N = k_- + 1 <= d + 1`.
     Then the head is at most one diagonal plus one orthogonality defect.
   - *Singleton:* `C_N(rho) != 0` once `2^N > k_-`, with a word of weight at most `k_- + 1`.
   - In general, with `D_N = max_(|w|=|w'|=N) ||rho(l^c_(w,w')) - 1||` and `d_N` the minimum weight of `C_N(rho)`,
     `||rho(x_13(c)) - 1|| <= min_N d_N · D_N`.
5. **Cohn shadow located.** For the exact model `λ rho_M` of `leavitt-cone-head-bound-is-finite-congruence-gluing` (5):
   - All four depth-1 relators `l^q_(i,j)` are trivial, as is `kappa`.
   - `t_2 t_1 -> e_12 e_11 = 0` is a weight-1 codeword at depth 2.
   - (RC) then forces the depth-2 diagonal relator `l^q_(12,12)` to carry the whole head. Indeed
     `s_1 s_2 q -> e_11 e_21 e_11 = 0`, so `λ rho_M(l^q_(12,12)) = λ rho_M(z)^(-1)`, at distance `sqrt 2`.
   - The shadow is invisible at depth 1 and fails at the first depth where its root code is nonzero.
6. **Mirror.** The same holds with the roles of `R_+` and `R_-` exchanged: codewords are dependences of the `s_w c`
   modulo `I_+`, and the relators are `l^c_(w_0, w)`.

**Consequence for (QC).**
- With `c = q` and normalized Hilbert–Schmidt norm, (RC) and the edge-invariance
  `c_* f_1 <= ||rho(z) - 1||_2^2` show that `f_1` is controlled by long Leavitt defects summed over any root codeword.
- Hence `(QC)` follows from two separate prerequisites, each of which can fail on its own:
  - **(LD_N)**: `delta`-small normal generators `k_i` force `D_N <= C(N) delta`.
  - **(BW)**: `delta`-small `k_i` force an `η`-codeword (item 3) at depth `N` and weight `m`, with `m·C(N)` and `η`
    bounded independently of `d`.
- Collision at depth `k_- + 1` always gives (BW) with `m = 2`, `η = 0`, but only at depth up to `d + 1`. A per-letter
  bound `C(N) = O(N)` then recovers exactly a head bound linear in `k_-`. That is the linear shadow-dimension head
  bound reported by the w20 lane (not landed in this worktree), now read off from a single weight-2 codeword.

**Class killed: exact-code uniformization at bounded depth.**
- *Class:* arguments that bound the head, uniformly in `d`, by long Leavitt relators of depth at most a fixed `N_0`,
  using only exact congruence data of `rho|Delta_-` (the ideal `I_-`, hence the codes `C_N(rho)`).
- *Invariant:* the truncation shadows `B_-^(M) = R_-/R_-^(>M)`, where `R_-^(>M)` is the span of all `t_w` and `q t_w`
  with `|w| > M`. This is a two-sided ideal, because `R_-` is the path algebra of a two-vertex quiver graded by
  path length (proof §4). In `B_-^(M)`, the words `t_w` with `|w| <= M` are linearly independent, so `C_N = 0` for
  every `N <= M`.
- *Death step:* the choice of a codeword at depth `<= N_0`, which does not exist once `M >= N_0`. Exact codes first
  appear at depth `M + 1`, which is unbounded over finite quotients.
- The census `experiments/leavitt-root-code-2026-09-17` confirms that the first codeword depth grows with the size of
  the matrix shadow. Over `M_k(F_2)`, `k <= 3` exhaustively and `k = 4` sampled, the weight-depth cost `min_N N·d_N`
  reaches 8 at `k = 4`, `r = 2`, with first codeword at depth 5.
- *What survives:* (BW) must be produced by `delta`-smallness itself, as `η`-near codewords in the `μ`-weighted
  Hamming geometry of item 3, not by ring data.

**What is not claimed.** Neither (LD_N) nor (BW) is proved here, so `(QC)` stays open. This does not show that bounded-depth
approaches fail for representations with small `k_i`. It shows only that exact root codes cannot supply them.
