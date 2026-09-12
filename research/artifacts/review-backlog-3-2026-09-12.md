# Review backlog, pass 3, 2026-09-12

Lane `review-backlog-3`. This pass reviews ESTABLISHED claims landed on 2026-09-12 before 15:00 that have no verdict yet. That excludes passes 1 and 2 (`review-backlog-2026-09-12.md`, `review-backlog-2-2026-09-12.md`) and every other review artifact on main. Claims landed after 15:00 belong to `swarm4-reviewer`.

Order of work:
1. the Kun–Thom rounding and unit-type chain to `non-hyperlinear-group`;
2. Leavitt rank-model nodes;
3. Thompson F;
4. Gottschalk table nodes.

**How the queue was built, at tip e367b4372:**
- start from the nodes first added between 00:00 and 15:00, not counting the restore commit 3f71a3a50;
- keep those marked ESTABLISHED in `research/FRONTIER.md`;
- drop every id that heads a section in any 2026-09-11 or 2026-09-12 review artifact.

69 claims remain.

**Verdicts:**
- **PASS:** the proof holds as written, up to its stated trust surfaces.
- **GAP:** a step is asserted but not proved, and the conclusion is not known to be false.
- **FAIL:** a step or the conclusion is false.

## 1. `root-character-nonunit-depth-at-most-log-q-dimension` (3a9a8d38e): PASS

Checked against `root-character-depth-log-dimension-proof` and §2 of
`nh-h1-quantitative-2026-09-12.md`.

- **Item 1, independence.**
  - Suppose `Σ_(i0<=i<k) c_i e_nu z^i ∈ J_χ` with `c_(i0) ≠ 0`. It factors as `e_nu z^(i0) u` with `u = c_(i0) + zw`.
  - Each local factor of `A_nu` is finite, with `z` in its maximal ideal, so `z` is nilpotent there. Hence the `A_nu`-component of `u` is a unit.
  - Multiplying by an element whose `A_nu`-component is `u^(-1)` stays inside the ideal `J_χ`. So `e_nu z^(i0) ∈ J_χ`, and then `e_nu z^(k-1)B ⊆ J_χ ⊆ ker χ`.
  - That makes `χ_nu` trivial on `z^(k-1)R_+`, contradicting minimality of `k`.
  - `J_χ` is an `F_q`-subspace because `F_q ⊆ B`. So `dim_(F_q) B/J_χ >= k`, and `|B/J_χ| >= q^k`.
- **Item 2, Heisenberg count.**
  - I re-derived the three Steinberg relations it uses, each needing `r >= 3`:
    - `[x_12, x_13] = 1`, since both lie in the same row;
    - `[x_12, x_32] = 1`, since `x_ij` and `x_kl` commute when `j ≠ k` and `i ≠ l`;
    - `[x_13(b), x_32(c)] = x_12(bc)`, by the rule `[x_ij(a), x_jk(b)] = x_ik(ab)` with `i ≠ k`.
  - On `V_χ` this gives `X(b)Y(c) = χ(bc)Y(c)X(b)`.
  - Let `v` be a joint eigenvector of `X(B)` with character `λ`. Then `Y(c)v ≠ 0` has character `b ↦ λ(b)χ(bc)`.
  - Two of these characters agree iff `χ(b(c−c')) = 1` for all `b`. That says `(c−c')B ⊆ ker χ`, which by definition is `c − c' ∈ J_χ`.
  - Distinct joint characters have orthogonal eigenspaces, so `dim V_χ >= |B/J_χ|`. The same argument runs inside any irreducible constituent whose `x_12`-spectrum contains `χ`.
- **Item 3.**
  - For the normalized spectral measure, `μ({χ}) = dim V_χ/N`.
  - Chaining the inequalities gives the display.
  - `D(π)` is at most `log_q` of the largest constituent dimension, which is at most `log_q N`.
- **Factorization through `St_r(B)`, a hypothesis the consumers need.** It holds automatically for every finite-image representation `π` of `EL_r(R_+)` with `r >= 3`, with no congruence subgroup property:
  - `J = {f : x_12(f) ∈ ker π}` is an ideal: `x_12(fb) = [x_13(f), x_32(b)]`, `ker π` is normal, and Weyl conjugation carries `x_12(f)` to `x_13(f)`;
  - `J` has finite index;
  - `St_r(R_+) → EL_r(R_+) → im π` kills every `x_ij(J)`, so it factors through `St_r(R_+/J)`.

  The components do not depend on the level (item "Components" of `nonunit-component-root-mass-is-log-scale-folner`), so `D(π)` is well defined.
- **Test case.** Take `d = 1` and `B = F_q[x]/(x^k)`, so `A_u = 0`, and let `χ` be nontrivial on `x^(k−1)B`.
  - The ideals of `B` are `x^iB`, so `J_χ = 0` and the bound reads `q^k <= dim V_χ`.
  - This matches Stone–von Neumann for the Heisenberg group over the finite local ring `B`: an irreducible representation with a central character that is nontrivial on the socle has dimension `|B| = q^k`.

## 2. `nonunit-root-mass-log-depth-scale-bound` (3a9a8d38e): PASS

Checked against `nonunit-root-mass-log-depth-proof` and §3 of the artifact.

- **The inputs match their statements on main.**
  - Item 3 of `nonunit-component-root-mass-is-log-scale-folner` (pass 1 §4) is exactly the per-scale cap
    `μ_n(d^j < depth_nu <= d^(j+1)) <= η_n` for `j >= 0`.
  - Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` (pass 1 §24) is
    `μ_n(depth_nu = 1) <= qη_n + η_n^t`, and its item 2 gives `η_n^t → 0` along `U`.
  - `nonunit-projection-bounded-by-root-spectral-mass` (pass 1 §2) bounds `τ(1 − P)` by
    `r(r−1)·μ(χ|A_nu ≠ 1)`, and `χ|A_nu ≠ 1` is the same event as `χ_nu ≠ 1`.
- **Item 1.**
  - By definition `D_n` is the largest depth on the support of `μ_n`, so no mass lies above it.
  - The blocks `(d^j, d^(j+1)]`, `j >= 0`, that meet `(1, D_n]` are those with `d^j < D_n`. There are `⌈log_d D_n⌉ <= 1 + log_d D_n` of them.
  - If `D_n <= 1`, the left side is 0.
- **Item 2.** `{χ_nu ≠ 1} = {depth_nu = 1} ⊔ {depth_nu > 1}`, because `depth_nu = 0` iff `χ_nu = 1`. Adding the two bounds gives the display exactly.
- **Item 3.**
  - `η_n → 0`, so the constant term vanishes.
  - `log max(1,D) <= log(1+D) <= log 2 + log max(1,D)`. So `η_n log_d max(1, D_n) → 0` iff `δ_n^2 log(1+D_n) → 0`.
  - With `D_n <= log_q n'` from §1 and `n'/n → 1`, it suffices that `δ_n^2 log log n → 0`.
- **Counterexample shape.**
  - Order-one mass `c` above depth one forces `log_d D_n >= c/η_n − 1`, so `D_n >= d^(c/η_n − 1)`.
  - The claim writes `>` where only `>=` follows. Nothing downstream uses strictness.
  - §1 then forces a constituent of dimension at least `q^(D_n)`.
- **Amplification.** The rate is correctly stated against `D_n`. Normalized HS distances, and the support of `μ_n`, do not change under `σ ↦ σ ⊗ 1_m` when the rounding is amplified along with `σ`.
