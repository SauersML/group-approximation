# UN review, part 4: the un-middle threshold theorems

Verifier `un-verify` (UN swarm), 2026-09-13. Subject: lane `un-middle`, landings `4db95cef51` and `486d277d93`.
Artifacts: `research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md` and `-part2.md`. Tip at review:
`172dd02250`.

| item | node | verdict |
|---|---|---|
| (1) | `paradoxical-ring-el-n-full-mf-radical-from-twice-level` (+ `-proof`) | PASS (same theorem as the canonical node) |
| (4) | `non-ibn-ring-el-n-full-mf-radical-above-module-rank` (+ `-proof`) | PASS after a one-sentence scope repair |
| (3) | `measure-free-ample-groupoid-el-n-full-mf-radical` (+ `-proof`) | PASS (same theorem as the canonical node) |

No false establishment of a main statement.

## 1. (1) Stable paradox threshold

**Step 1: a full complement in `S = M_n(R)`.** Take `θ : R^n → R^n ⊕ P` with `P = R ⊕ Q`, `s = θ⁻¹ι` and `t = πθ`.
Then `ts = πι = 1`, and `e = 1 − st = θ⁻¹ι_Pπ_Pθ`. With `x_i = ε_iαπ_Pθ` and `y_i = θ⁻¹ι_Pβδ_i`,
`x_i e y_i = ε_iα(π_Pι_P)(π_Pι_P)βδ_i = ε_iδ_i = e_ii`, so `1 = Σ x_i e y_i`. Checked.

**Steps 2–4.**
- `full-defect-ring-non-mf-at-rank-two` applies to `S`.
- The corner map `M_2(S) → M_N(R)` sends `e_12(X)` to `Π_{a,b} e_{a,n+b}(X_ab)`. These factors commute, because
  `E_{a,n+b}E_{a′,n+b′} = 0` as `n+b ≠ a′`.
- `e_{1,n+1}(r)` is the image of `e_12(rE_11)`.
- Signed permutations `w_kl = e_kl(1)e_lk(−1)e_kl(1)` carry it to every `e_ij(±r)`.

All checked.

**Calibrations checked.**
- `L_k(1,m)`: level 1.
- `L_k(m,n)`: `R^m ≅ R^{m+1} ⊕ R^{n−m−1}`, so the level is at most `m`.
- The Pestov ring has a state at `[R]` from normalized matrix rank, so the theorem is silent.
- Fields: never.

**Duplicate.** Since the un-architect ruling (`b9ba6293f`), this node points at the canonical
`stably-infinite-ring-elementary-groups-have-no-mf-quotient`, reviewed PASS in part 3 §1. The hypotheses agree at the
same `n`.

## 2. (4) Non-IBN rank reduction

**(1).** `R^m ≅ R^{m+d} = R^{m+1} ⊕ R^{d−1}` gives `(m+1)[R] ≤ m[R]`, hence full MF radical from rank `2m`.
Iterating gives `R^m ≅ R^{m+jd}`.

**(2).** With `f = N − m ≥ 1`, the maps `A = diag(X, 1_f)` (size `N × M`) and `B = diag(Y, 1_f)` (size `M × N`),
where `M = N + jd`, satisfy `AB = diag(XY, 1) = 1_N` and `BA = 1_M`. So `Φ(g) = AgB` is an isomorphism
`GL_M → GL_N` with inverse `h ↦ BhA`. Checked.

**(3).** Here `c = m+jd+1` and `c′ = m+1`.
- Column `c` of `A` and row `c` of `B` are unit vectors at `c′`.
- `Φ(e_{ic}(r)) = 1 + (col_i A) r (row_c B) = 1 + Σ_k E_{kc′} x_ki r = Π_k e_{kc′}(x_ki r)`. The factors share the
  column `c′ ∉ {k}` and commute.
- `Φ(e_{ci}(r)) = Π_k e_{c′k}(r y_ik)`.
- Free–free roots go to free–free roots.
- `e_ij(r) = [e_ic(r), e_cj(1)]` for distinct `i, c, j`. Every other free index is handled the same way.

So `Φ(EL_M(R)) ⊆ EL_N(R)`. Checked.

**(4).** `ker φ ∋ g_i(r) = Π_k e_{kc′}(x_ki r)`.
- **`m = 1`:** `Π_i e_{1c′}(x_1i y_i1) = e_{1c′}((XY)_11) = e_{1c′}(1)`.
- **`m ≥ 2`:** `e_{kk′}(s)` commutes with `e_{lc′}` for `l ≠ k′`, and
  `(1+sE_{kk′})(1+bE_{k′c′})(1−sE_{kk′}) = 1 + bE_{k′c′} + sbE_{kc′}`, recomputed. So the commutator isolates
  `e_{kc′}(s x_{k′i} r)`. Taking `s = 1`, `r = y_{ik′}` and multiplying over `i` gives `e_{kc′}((XY)_{k′k′}) = e_{kc′}(1)`.
- **Normal generation (`N ≥ 3`):** `[e_{ak}(r), e_{kc′}(1)] = e_{ac′}(r)` for `a ∉ {k, c′}`, then
  `[e_{ka}(r), e_{ac′}(1)] = e_{kc′}(r)`, then signed permutations.

All checked.

**Use for `L_k(2,3)`.** `R^2 ≅ R^3` by the defining relations (`m = 2`, `d = 1`), so `N ≥ max(3,3) = 3`. Checked.
- Cohn's `(m−1)`-fir theorem and Bergman's IBN-failure pattern appear only in "Recalled, not verified" remarks. The
  route requires only `paradoxical-ring-el-n-full-mf-radical-from-twice-level`, so neither is load-bearing.

**Scope repair (applied by un-verify).** The instance bullet said "these are finitely generated Kazhdan groups" with
no condition on `k`. `L_k(2,3)` is a finitely generated ring only when `k` is finite, since a field that is finitely
generated as a ring is finite. For infinite `k`, `EL_N(L_k(2,3))` is not finitely generated and has no (T), for the
reason given in part 3 §4.
- The bullet now reads "Over a finite field `k`, with EJZ, these are finitely generated Kazhdan groups …". The main
  statement is unchanged.
- The same slip appears in the artifacts: part 1 §5 ("`EL_3(L_k(2,3))` is finitely generated with property (T)") and
  part 2 §3. Those are lane prose; the node is authoritative.

**Subsumption scan (untruncated).** Claims matching IBN / invariant basis number / module type / `L(2,3)` /
`R^m ≅ R^{m+d}` / rank condition: 44 claims read by title and status. None states the non-IBN rank reduction.
- `mf-rigidity-is-monotone-in-matrix-rank` (full MF radical is an up-set in the rank) is consistent with it.
- The open neighbour `el-n-mf-quotient-below-twice-paradoxical-level-exists` already records the `L_k(2,3)` candidate
  as dead through this node.

## 3. (3) Measure-free ample groupoids

- Put `m(U) = ν([1_U R])`.
  - It is additive, since `1_{U⊔V}R = 1_U R ⊕ 1_V R`.
  - It is monotone and finite, with `m(U) ≤ m(X) = 1`.
  - It is invariant, since `1_B1_{B⁻¹} = 1_{r(B)}`.
- A finitely additive measure on the clopen algebra of a compact zero-dimensional space is countably additive there:
  a countable disjoint clopen cover of a clopen set is finite. So Carathéodory gives a Borel probability, and it is
  invariant on compact open bisections as the node defines. With no invariant measure, KMP Tarski gives the paradox and
  (1) applies.
- "When `R` is finitely generated" correctly conditions the (T) sentence.
- **Examples.**
  - A paradoxical nonempty compact open set in a minimal groupoid forces `μ(U) = 0`, which contradicts full support.
  - The Boldrini–Prasad rings are not finitely generated, as stated.
- **Duplicate.** It points at the canonical `no-invariant-measure-steinberg-elementary-no-mf-quotient` (part 3 §3).

## 4. Display check

Recomputed:
- `x_i e y_i = e_ii`;
- `e_12(X) ↦ Π e_{a,n+b}(X_ab)`;
- `AB = 1_N`, `BA = 1_M`;
- `Φ(e_{ic}(r)) = Π_k e_{kc′}(x_ki r)` and `Φ(e_{ci}(r)) = Π_k e_{c′k}(r y_ik)`;
- the conjugation identity `e_{kk′}(s)e_{k′c′}(b)e_{kk′}(−s) = e_{kc′}(sb)e_{k′c′}(b)`;
- `m(r(B)) = m(s(B))`.

All correct.
