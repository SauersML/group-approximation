# EX review wave 2, part 18: Ihara--Bass traces, Deligne floors, Bernoulli tubes (census priority E, 2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. Census: part 11. This part
finishes the wave-2 census.

**Blobs.** Rechecked at tip `6e48d1a67a`.
- **ex2-cubic-ihara-bass:**
  - `cubic-division-congruence-outliers-delocalise-at-log-scale` (`c3eaeed1e`, route `f39e609ac`);
  - `cubic-division-ihara-traces-count-roots-mod-p` and `free-group-ihara-bass-outlier-trace-criterion` (`4bc844355`).
- **ex2-nh-deligne-sector-floor:** `deligne-monomial-cover-models-have-a-detecting-cycle-floor` (`0d1a6d46f`).
- **ex2-bc-cylinder-comparison:** `bernoulli-defects-vanish-along-bcc-subgroup-tubes` (`6443f37ad`), with its artifact
  `bc-bernoulli-subgroup-restriction-2026-09-13.md`.

**Prerequisites.**
- With PASS:
  - `cubic-division-congruence-sc-descends-to-thin-subgroups` (part 6);
  - `deligne-covers-of-sp2g-z-have-finite-residual-2z` (part 7);
  - the three Bernoulli comparison nodes (part 7).
- Reviewed here: `finitely-generated-linear-groups-are-residually-finite` (Malcev), which was established without a
  PASS.
- `cubic-division-congruence-representations-converge-strongly` is OPEN. It is cited only for notation.

## 18.1 Verdicts

| claim | verdict |
|---|---|
| `finitely-generated-linear-groups-are-residually-finite` (import: Malcev 1940, Wehrfritz Ch. 4) | PASS |
| `free-group-ihara-bass-outlier-trace-criterion` | PASS |
| `cubic-division-ihara-traces-count-roots-mod-p` | PASS |
| `cubic-division-congruence-outliers-delocalise-at-log-scale` | PASS |
| `deligne-monomial-cover-models-have-a-detecting-cycle-floor` | PASS |
| `bernoulli-defects-vanish-along-bcc-subgroup-tubes` | PASS |

No root flips. Strong convergence for cubic division lattices, non-hyperlinearity of Deligne covers, and Bernoulli
Baum--Connes stay open.

## 18.2 Re-derivations

**Ihara--Bass criterion.**
- **The operator.** `B = D(TT^* − Q)`. `tr B^n` sums `χ(s_0^{−1}⋯s_{n−1}^{−1})` over cyclic non-backtracking sequences,
  which biject with `CR_n`.
- **The determinant.**
  - `J = DQ` satisfies `J^2 = I` and `tr J = 0`, so `det(I + uJ) = (1 − u^2)^{kd}`.
  - `JDT = T`, `T^*DT = Z` and `T^*T = 2k`, so Sylvester gives
    `det(I − uB) = (1 − u^2)^{(k−1)d} det((1 + qu^2)I − uZ)`.
  - The degree `2kd` matches, so no eigenvalue is lost.
- **Part 3.** The generating function `Σ_ν m_ν νu/(1 − νu)` has simple poles with nonzero residues. Cauchy--Hadamard
  gives `limsup |E(n)|^{1/n} = M_ρ`, and `|λ| = |μ| + q/|μ|` for real roots.
- **Part 4(b).** At even `n` the real outlier roots contribute `ν^n > 0`. So `M^n ≤ E(n) + 2dq^{n/2}`.

**Traces count roots mod p.**
- **Part 1.** `Q(w)` is a subfield of degree dividing 3. `Q(w) = Q` would force `w^3 = 1` with `w` rational, so `w = 1`.
  The reduced characteristic polynomial is then minimal, and `Δ(w) = f_w(1) ≠ 0`.
- **Fixed points.** Lines fixed by `g` are eigenlines with eigenvalues in `F_p`. `d_1 ≥ 2` together with `det g = 1`
  forces unipotence of rank `≤ 1`.
- **The counting identity.** `p^{d_1} − 2 = −1 + (p − 1)[d_1 ≥ 1] + (p^2 − p)[d_1 ≥ 2] + (p^3 − p^2)[d_1 = 3]`, checked at
  `d_1 = 0..3`.
- **Part 4.** Here `E(n) = T(n) − d(1 + (−1)^n)` and the left side of (b) is `E(n) + 2 + (−1)^n + (p^3 − 2)(1 + (−1)^n)`.
  Both converses use positivity at even `n`, and `log d = O(log p)`.
- **Part 5.**
  - Dedekind--Kummer applies with `disc(f_w) = [O_E : Z[w]]^2 disc(E)`.
  - Chebotarev gives mean `⟨ρ_E, 1⟩ = 0` and multiplicities `m_E = 1, 2`.
  - Each primitive conjugacy class contributes `n^2` to `V_n`.

**Delocalisation at log scale.**
- **Two non-commuting units generate `D`.**
  - The algebra `S` they generate is a division algebra of degree `m ≥ 2` over its centre `F`.
  - The double centraliser theorem gives `m^2[F : Q] | 9`, so `S = D`, and `V_8 = D` by dimension.
- **Part 1.**
  - A non-cyclic `π_1(B(x, R)) = Stab_H(x) ∩ π_1` contains two non-commuting fundamental loops of length `≤ 2R + 1`.
  - Nine independent products of length `≤ 8(2R + 1)` lie in the 7-dimensional line stabiliser mod `p`, so `p | δ`.
  - The size bound is `|δ| ≤ 9!C_0^9 ρ^{72(2R+1)}`. `ρ > 1`, because `Γ_D` is discrete in `SL_3(R)`.
- **Part 2.**
  - When `w^d` is regular semisimple, `g` preserves its eigenlines, so rational fixed points of `g^d` are fixed by `g`.
  - `disc(f_{w^d}) ≠ 0` with `|disc| ≤ (2ρ^{dL})^6`.
- **Part 3.**
  - Complete `B(x, R)` by trees to the Schreier graph of `F_2/Q`, where `Q` is cyclic, hence amenable. The spectrum lies
    in `[−2√3, 2√3]`.
  - The cutoff `χ` has Lipschitz constant `2/R`, and `(A_U − λ)(χf) = [A, χ]f`, whose four terms each have norm
    `≤ (2/R)‖f1_{B(x,R+1)}‖`.

**Detecting-cycle floor.**
- **Step 1.** Exact permutations make the relator unitaries diagonal with entries `exp(2πi δa)`. With
  `|sin πt| ≥ 2|t|`, `(1/d)Σ_x c^2 ≤ η_r^2/16`.
- **Step 2.** `⟨δa, Σ⟩ = 0` gives `|⟨c, Σ⟩| ≥ ν(Σ)`.
- **Step 3.**
  - Right multiplication by `Γ/N` gives `d` cellular translates. The mass redistributes as `μ_r`.
  - Summing, then Cauchy--Schwarz and (P1), gives `d·ν ≤ d|Σ|_1 max_r η_r/4`.
- **Steps 4--5.** Pullback to the normal core has uniform fibres. For several orbits the bound averages over `R`.
- **Step 6.**
  - `H^2(Y; R/Z) = Hom(H_2(Y; Z), R/Z)`. With no detecting cycle, `θk = δa mod Z`, which gives an honest representation
    with `z ↦ ζI`.
  - Malcev then gives a finite quotient not killing `z^2`, which contradicts (DR2).
- **Step 7.**
  - Some component of a detecting cycle is detecting, and it has `≤ AL` edges.
  - Loops of length `≤ 2AL + 1 < sys(N)` lift to the Cayley complex, where integral cycles are spherical.
  - Identities among relations give `z^{⟨k,Σ⟩} = 1` in `Γ~`, and `z` has infinite order there.

**Bernoulli tubes.**
- **Lemma 1.** `π_x(fu_g)δ_k = f(gk^{−1}·x)δ_{kg^{−1}}` is nonzero only if `x_{kg^{−1}w} ≠ 0` for some `w ∈ W`. So the row
  and column indices lie in `HFW^{−1}(E ∪ {e})`, a union of right `H`-cosets.
- **Proposition 3.**
  - The entry check `h c_j g^{−1} = h'c_i ⟹ φ_i(ηh^{−1}·x)` holds.
  - The family `(ψ_x)_{x∈X_Y}` is faithful on the reduced crossed product, being induced from the faithful `⊕ ev_x`.
  - So `Res` is a contractive `*`-homomorphism on the dense union, and it extends.
- **Proposition 4.** Ranks are preserved, and `π_x(1_{C_s})` is diagonal at `k ∈ K_s`, a finite union of right cosets.
- **Theorem 5.**
  - `K_1` of the target is `T_r(0) = 0`.
  - The Möbius formula of RF R5 uses only ranks at sub-patterns inside `Y`, which gives `n_t(y) = m_{[t]_H}`.
- **Corollary 6.** `g t ⊆ HF` forces `g ∈ HFf^{−1}`.

## 18.3 Notes

- **Not re-read here** (flagged by the owners): Chebotarev (Neukirch VII §13); the Poisson cycle counts of random words
  (a remark, not used); RF Lemmas R1--R5 for free `H`-sets; CEKN Theorem 2.8.
- **No owner notes** for this batch.

## 18.4 Outcome of the wave-2 census (parts 11--18)

- **Coverage.** Census 33 claims plus imports.
  - Parts 12--18 give PASS to all 33, and to the unreviewed established imports met along the way: Jiang, the Izumi
    duality through Barlak--Li, and Malcev.
  - Before the census: part 9 (Pauli W*-bundle, CCEGSTW Q1.5/Q5.29) and part 10 (Rainone) are PASS.
- **One GAP.** In the norm-functor proof at odd p (part 12). It is repaired by citation of Nishikawa--Petrosyan
  (§12.5), and credit for items 1--3 moves to them.
- **Wording notes sent** to rank-monotone-rounding (three), unitary-class-five (stem-0 letters) and bk-relative-lemma-b
  (stale condition).
- **No false establishment.** The roots touched by these lanes stay as they were:
  - the W*-bundle root is established, with PASS;
  - LXI and XXIX are open.
