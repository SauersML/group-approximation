# sk-verify-11 part 1: independent second review of the universal LEF host (rev4 item 71(d))

Lane sk-verify-11 (ROSTER-H, wave 10), 2026-09-13 ~21:50 CDT. Independent second review of the inputs to rev4 item 71(d), rechecked by hand.

**Scope.**
- sk-universal-lef-host-b (a303f6663a): Lemma A, Theorems B and C, Proposition D.
- sk-universal-lef-host-a: the wreath-product Lemma A, A1 (the iff), and A2 (no quotient doubling).
- sk-wp-host (39a1b8550b): Theorems A and B. Theorem B is in this part; the source check behind Theorem A is in part 2.
- The printed text of item (d) in sk-editor-4's draft `sk/drafts/rev4-partC.tex` (21:40): part 2.

**Independence.**
- I did not open `sk-review-7-*` or `sk-review-8-*`.
- The claim nodes on main already carry one-line review stamps from those lanes. I saw the stamps and used none of their content.

Verdict scale: PASS / PASS-WITH-FIXES (verbatim) / FAIL.

## 1. `countable-lef-groups-embed-in-two-generator-lef-groups` (host-b Lemma A): PASS
I re-derived host-b's §1 by hand.

**Step 1 (models).** LEF applied to the finite set `F_k ∪ F_k F_k` gives maps that are injective on `F_k` and multiplicative for all `g, h ∈ F_k`. That is the form of (M) that host-b uses.
- The weaker form "`φ_k(gh) = φ_k(g)φ_k(h)` when `g, h, gh ∈ F_k`" also suffices. For fixed `g, h` the product `gh` is some `γ_m`, so all three lie in `F_k` once `k ≥ m`.
- `φ_k(1) = 1` follows from `1·1 = 1` inside `F_k`.
- (I) follows from injectivity against `1 ∈ F_k`.

**Step 2 (Ore).** A doubled left-regular permutation has every cycle twice, so it is even.
- Ore, Theorem 1 (import node, two PASSes, JSTOR quote p. 308) holds for every n. The degenerate set `|Q_k × {1,2}| = 2` is fine: the identity is `[id,id]`.
- The commutator convention is immaterial: `aba⁻¹b⁻¹ = x⁻¹y⁻¹xy` with `x = a⁻¹`, `y = b⁻¹`. The same convention is used for the Ore data and for `w_j`.

**Step 4 (conjugation).** Composing as functions: `b^n(x,i) = (x, i+n)`, `a(x, i+n) = (τ_{i+n}(x), i+n)`, and `b^{-n}` returns this to level `i`. So `b^{-n} a b^n` acts on level `i` by `τ_{i+n}`. ✓

**Step 5 (isolation).** On level `i`, `w_j(a_k,b_k)` acts by `[τ_{i+p_j}, τ_{i+q_j}]`, which is trivial unless both residues lie in `P_k`.
- Suppose `i+p_j ≡ s′` and `i+q_j ≡ s` with `s, s′ ∈ P_k`. Then `(q_j − p_j) − (s − s′) ≡ 0 (mod 4^{k+1})`.
- Both terms have absolute value below `4^k`, so the left side has absolute value below `2·4^k < 4^{k+1}`, and it vanishes in `Z`. Wrap-around is covered by this bound.
- `s − s′ = 2^{2j} − 2^{2j−1} > 0`. The 2-adic valuation of `2^c − 2^d` (with `c > d`) is `d`, so `d = 2j−1`, `c = 2j`, and `i ≡ 0`.
- On level 0 the word gives `[α_{jk}, β_{jk}] = π_k(γ_j)`.

**Steps 6–8.**
- The ultraproduct map is a homomorphism by (M) on an ω-large (cofinite) set, and injective by (I). Left multiplication by `φ_k(g) ≠ 1` moves every point.
- `w_j(a,b) = ι(γ_j)`, since the two agree for `k ≥ j`.
- Every subgroup of an algebraic ultraproduct of finite groups is LEF. For a finite `A`, the finitely many identities and inequalities hold on a set in ω, so at some coordinate `u ↦ u(k)` is an injective partial homomorphism.
- `Δ ⊇ ι(Γ)` is infinite when `Γ` is.

**Model tests.**
- `Γ = BS(2,3)`: finitely presented and not residually finite, so not LEF. Step 1 has no models, and indeed `Δ` would be LEF, so no such `Δ` can exist.
- `Γ` finite: trivial.
- `Γ = ⊕_n Alt(n)`: countable but not finitely generated. The construction uses only an enumeration, so it applies.
- An exhaustive residue check is unnecessary: the congruence-to-equality bound above is exact.

**Merged sentence** "`ι(Γ) ≤ [Δ,Δ]`": PASS, since each `ι(γ_j)` is the commutator `w_j(a,b)`.

## 2. `countable-lef-groups-embed-in-simple-kazhdan-lef-groups` (host-b Theorem B): PASS
- `Γ × Z` is LEF: take the product of a partial model on the projection `A` with `Z → Z/N` injective on the second projection `B`. It is injective on `A × B`, and a product inside `F` forces the first coordinates into `A`.
- Lemma A puts `Γ × Z` in a 2-generated infinite LEF `Δ`.
- `lef-groups-embed-in-simple-kazhdan-lef-groups` takes any f.g. LEF input, so the composition is valid.
- ⇐: subgroups of LEF groups are LEF.

## 3. `simple-kazhdan-lef-host-for-recursive-lef-groups` (host-b Theorem C): PASS
**(a)** The restricted sum is countable. A finite subset lies in a finite subproduct, and products of partial models are partial models.

**(b)** There are countably many r.e. relator sets on finitely many generators, hence countably many types.

**Examples.**
- f.p. RF groups: f.p. ⇒ recursively presented, RF ⇒ LEF. ✓
- `G_Y` with recursive language: the WP degree node (PASS) gives solvable WP, hence recursive presentation. ✓
- f.g. linear groups: the node routes them through "recursively presented" (Rabin, recalled). This detour is unnecessary: f.g. linear groups are RF (Mal'cev) and have countably many types (f.g. fields), so part (a) applies directly. Rev4's printed proof uses exactly that route (partC l.128–131), so no recalled input reaches the note.
- `[[T]]′`: recalled and illustrative only; the route does not require it.

**Sharpness** (`no-countable-group-contains-all-fg-lef-groups`): PASS. A countable group has countably many finite subsets, hence countably many f.g. subgroups, while the reviewed Turing-degree node gives continuum many `G_X`.

**Model test.** Without countability the statement fails for the Sturmian family (continuum many types), as Proposition D says. Recursive presentation enters ONLY through countability.

## 4. sk-universal-lef-host-a
**Lemma A (wreath form, artifact §1): PASS.**
- `σ ↦ στ^{ε(σ)}` is an injective homomorphism `Sym(k) → Alt(k+2)`: `τ` commutes with `σ` and `ε` is additive.
- `(t^{-s} f t^s)(k) = f(k+s)` follows from `(t f t^{-1})(k) = f(k−1)`.
- The binary identity `2^α + 2^δ = 2^γ + 2^β` forces `{α,δ} = {γ,β}`; the case `α = δ` forces all four equal, which is excluded.
- `|s_α − s_β|` and `|s_{2i−1} − s_{2i}|` are each at most `2^{2n}`, so their difference is below `2^{2n+1} < N_n = 2^{2n+3}`.
- Coordinatewise commutators in the base; ultraproduct as in §1.
- **Nit** (no effect): "`m_n ≥ 5`" fails when `K_n` is trivial (`m_n = 3`). It is never used, because Ore's Theorem 1 holds for every `n`.

**A1** (`simple-kazhdan-lef-host-iff-lef-and-countably-many-types`): PASS.
- (1)⇒(2): a f.g. host is countable.
- (2)⇒(3): LEF passes to subgroups, and a countable group has countably many f.g. subgroups.
- (3)⇒(1): Theorem C(a) applied to representatives.
- Model tests:
  - `𝒞` = all finite groups: countably many types, all LEF, so one host contains every finite group. This is consistent, since any `G_X` already contains `GL_d(F_2)` for all `d`.
  - `𝒞` = all Sturmian `G_X`: fails (3) and has no host. ✓

**A2** (route `lef-groups-embed-via-two-generator-lef-envelope`): PASS.
- `ι(Γ) ≤ [Δ,Δ] ≤ [L,L]` with `Δ ≤ L`.
- Over `F_2`: `e_12(c)e_21(c⁻¹)e_12(c) = [[0,c],[c⁻¹,0]]`, because `1 + cc⁻¹ = 0`. Multiplying by `e_12(1)e_21(1)e_12(1) = [[0,1],[1,0]]` gives `diag(c, c⁻¹)`.
- `diag(c,c⁻¹,1) diag(c′,c′⁻¹,1) diag((c′c)⁻¹, c′c, 1) = diag(cc′c⁻¹c′⁻¹, 1, 1)`. The first entry is `c c′ (c′c)⁻¹`; the second is `c⁻¹c′⁻¹c′c = 1`.
- `ξ ↦ diag(u_ξ,1,1)` is a homomorphism, so products of commutators land in `E_3`.
- Firewall: neither `a ↦ diag(a,a⁻¹,1)` as a homomorphism nor the double swap is used.
- The quotient-doubling paragraph is genuinely unnecessary once Lemma A gives `Γ ≤ [Δ,Δ]`. Rev4's partC already follows A2.

## 5. `recursive-lef-growth-hosts-miss-some-fp-rf-group` (sk-wp-host Theorem B): PASS
I re-derived Steps 1–6 of the route.
- **Step 3** is the key step. With the prefix induction `ψ(v) = φ(v̄)` on the ball, every relator of length at most `m ≤ n` maps to `φ(1) = 1`. So the partial model extends to a homomorphism `Γ → Q` that agrees with it on `B_Γ(n)`. Injectivity on the ball then separates every pair of words of length at most `n`, giving `ρ_Γ(n) ≤ L_Γ(n)`.
- **Step 2:** `L_Γ(r) ≤ L_U(Cr)` by restriction.
- **Step 4:**
  - `h` is made monotone, and `f(n) = h(n²)`;
  - for `n ≥ max(m, C)`: `ρ_Γ(n) ≤ L_U(Cn) ≤ h(n²) = f(n) < ρ_Γ(n)`, a contradiction;
  - the depth is computed on the fixed generating set where KMS's inequality holds, so no change-of-generators equivalence is needed.
- **Step 6 (LEF + solvable WP ⇒ `L_U` recursive):** tabulate the ball using the WP, then search groups of increasing order; the search halts because `U` is LEF.
- **Source.** In my own fetch of arXiv:1204.6506v5 on MSI (`KMS-322.tex`, gzip, 121286 bytes), the theorem `\label{t:rhog}` (l.1381) matches the quote in `kms-fp-rf-groups-with-arbitrarily-large-depth-citation`: "For every recursive function $f$ there exists a finitely presented residually finite …, [with $\rho_G(n)>f(n)$ for] all $n$".
- **Model tests:**
  - `U` finite: `L_U` bounded, and `U` misses `Z`. ✓
  - `U = Z`: `L_U(r) = 2r+1`, and `U` misses `F_2`. ✓
  - The universal host of §3 contains all f.p. RF groups, so its LEF growth must be non-recursive. That is consistent: its models come from non-effective ultraproduct data.
  - A `G_Y` with recursive language is LEF with solvable WP, so it misses some f.p. RF group. That is consistent with §3, which uses a different host.

Part 2 covers `no-decidable-group-contains-every-fp-rf-group`, the KMS time-complexity definition checked at source, and the rev4 printed text of item (d).
