# SK verify 13, part 1: four non-confinement claims for test subgroups of G_X (sk-cstar-simple)

Lane sk-verify-13 (wave 10), 2026-09-13. It serves `sk/queue/sk-verify-13.txt`. Main rescoped this lane at ~21:55: the
sk-measured-subshift Theorems A/B and the sk-matricial-stability claims already PASSed in sk-verify-7 part4 (6ab268edd3),
so they are skipped here, and the sk-cstar-simple claims (5b5d267149, 8c01032729, 0da354bcb9) come first.

Every step below was re-derived by hand from the route nodes on main. Throughout: `R = LC(X,k) ⋊_T Z`,
`u f u^{-1} = f∘T^{-1}`, `[g,h] = ghg^{-1}h^{-1}`. A subgroup `H ≤ G` is confined if some finite `P ⊆ G∖{1}` meets every
conjugate of `H` (`cstar-simple-iff-amenable-subgroups-not-confined`).

## 0. Verdicts

| claim | verdict |
|---|---|
| `elementary-root-subgroups-over-crossed-products-are-not-confined` | PASS |
| `locally-constant-gl-n-subgroup-is-not-confined` | PASS |
| `topological-full-group-images-in-el3-are-not-confined` | PASS (general statement); its Instances are conditional on an unreviewed node |
| `cut-stabilizer-subgroups-of-el3-are-not-confined` | PASS |

**Scope.** These show that none of the listed test subgroups is an obstruction to C*-simplicity through Kennedy's criterion.
They do NOT prove C*-simplicity, since a nontrivial amenable uniformly recurrent subgroup might come from elsewhere.
`subshift-elementary-groups-are-cstar-simple` correctly stays OPEN.

**Incidental (before the rescope).** I had independently re-derived Theorem A of sk-measured-subshift and found it correct,
in agreement with sk-verify-7. One simplification: `x_p(h) = c(v·h)` is defined for every `h ∈ Δ`, so `x_p ∈ 2^Δ` and
`D_k(f)e_p = f(x_p)e_p` needs no windows. Then `Φ_k` is exactly linear, and windows enter only in the localization.

## 1. Root subgroups

**Lemma A.** If conjugates `k_mHk_m^{-1}` (`m ≥ 1`) intersect pairwise trivially, each `p ∈ P` lies in at most one of them,
so some conjugate misses the finite set `P`.

**Heredity.** A set confining `K ≤ H` meets `gKg^{-1} ⊆ gHg^{-1}` for all `g`, so it confines `H`. So subgroups of
non-confined subgroups are not confined.

**Lemma B.** Write `u^N − u^M = u^M(u^d − 1)` with `d = N − M ≠ 0`.
- If `r = Σ_{j∈S} f_j u^j ≠ 0` with every `f_j ≠ 0`, then `u^d r = Σ_j (f_j∘T^{-d}) u^{j+d}`.
- For `d > 0`, the exponent `max S + d` carries the coefficient `f_{max S}∘T^{-d} ≠ 0` (`T` is a homeomorphism), and `r`
  has no such term. For `d < 0` use `min S`.
- So `(u^N − u^M)r = 0` forces `r = 0`.

**Conjugates.**
- The Steinberg relation for the distinct indices `3,1,2` gives `[e_31(s), e_12(r)] = e_32(sr)`.
- So `k_N e_12(r) k_N^{-1} = e_32(u^N r) e_12(r) = I + u^N r E_32 + r E_12`, because `E_32E_12 = 0`.
- If this equals `I + u^M r' E_32 + r' E_12` with `N ≠ M`, then the `(1,2)` entries give `r = r'` and the `(3,2)` entries
  give `(u^N − u^M)r = 0`, so `r = 0`.

**Reduction.** Weyl elements `e_ij(1)e_ji(−1)e_ij(1)` lie in `EL_n(R)` and conjugate `e_12(R)` onto `e_ij(R)` (the sign is
absorbed, since `e_ij(R) = e_ij(−R)`). Confinement is conjugation invariant.

**Model test.**
- Finite groups: every subgroup is confined (`P = G∖{1}`), and Lemma B fails for `u ↦` a permutation matrix of finite order.
- The claim uses neither infiniteness nor minimality of `X`, and it stays true for the trivial action, where `R` is a
  Laurent polynomial ring over `LC(X,k)`. That is consistent.

## 2. Locally constant GL_n over F_2

**Step 1.**
- `ψ_i(x) = (1 − e_{C_i})I + e_{C_i}x` is unital and multiplicative on `M_n(F_2)`: the entries of `x` are scalars and commute
  with `e_{C_i}`, and `e^2 = e`.
- `ψ_i(e_jk(1)) = e_jk(e_{C_i})`, and `GL_n(F_2) = SL_n(F_2) = E_n(F_2)`.
- The factors commute and multiply to `Σ_i e_{C_i}g_i`, because the `C_i` partition `X`.

**Step 2.**
- With `ε_i = 2i − n − 1` and `s_i = ε_1 + … + ε_i` (so `s_n = 0`), position `i` of `∏_i d_i(u^{s_iN})` carries
  `u^{(s_i − s_{i−1})N} = u^{ε_iN}`.
- Whitehead over a noncommutative ring:
  `e_12(a)e_21(−a^{-1})e_12(a) = [[0,a],[−a^{-1},0]]`, and times `[[0,−1],[1,0]]` this is `diag(a,a^{-1})`.
  I checked both products entrywise.

**Step 3.**
- `u^m f = (f∘T^{-m})u^m`, so `(c_Ngc_N^{-1})_{ij} = (g_ij∘T^{−ε_iN}) u^{(ε_i−ε_j)N}`.
- For `i ≠ j` and `N ≠ M` the exponents differ, so equality of conjugates forces `g_ij = g'_ij = 0`.
- An invertible diagonal matrix over the commutative ring `LC(X,F_2)` has unit entries, and `LC(X,F_2)^× = {1}`.

**Model test.** Over `F_3` the torus `diag(LC(X,F_3^×))` commutes with every `c_N`, so the proof must fail there, and the
scope note excludes it.

## 3. Images of the topological full group

**Computation.** For `s = u^N`:
- `(I + sE_31)p = p + saE_31`, since row 1 of `p = diag(a,b,1)` is `(a,0,0)`.
- `p·sE_31 = sE_31`, since column 3 of `p` is `e_3`, and `E_31E_31 = 0`.
- So `k_Npk_N^{-1} = p + u^N(a − 1)E_31`.
- Equal conjugates for `N ≠ M` force `a = a'`, `b = b'` and `(u^N − u^M)(a − 1) = 0`, so `a = 1` by Lemma B and `p = I` by
  injectivity of the first coordinate.

**Condition.** The Instances need `diag(w_g,1,1) ∈ EL_3(R)` on `[[T]]′` and `diag(w_g,u^{−I(g)},1) ∈ EL_3(R)` on `[[T]]`.
- This is `topological-full-group-embeds-in-subshift-elementary-group`, which is ESTABLISHED (unreviewed; queued with
  sk-referee-2).
- The general statement does not depend on it.
- Suggested wording for the claim node (0 lines): "Instances (conditional on the unreviewed …)".

**Firewall** (the node's own, re-checked): `diag(1,b,1)` commutes with `e_31(r)`, so injectivity of the first coordinate is
needed.

## 4. The half-orbit cut stabilizer

**π_y and S_y.**
- `π_y((fu^k)(gu^m))δ_t = f(T^{t+k+m}y)g(T^{t+m}y)δ_{t+k+m} = π_y(fu^k)π_y(gu^m)δ_t`.
- `S_y` is a subgroup: an invertible operator preserving both summands of the direct sum `(V^{<0})^3 ⊕ (V^{≥0})^3` has an
  inverse that preserves them too.
- Membership is entrywise, as the node says.

**Lemma C.**
- The entry `u^{−N_i}q_iju^{N_j}` acts as `σ^{−N_i}π_y(q_ij)σ^{N_j}`. It preserves both half-spaces iff `π_y(q_ij)` maps
  `V^{≥N_j} → V^{≥N_i}` and `V^{<N_j} → V^{<N_i}`.
- **Case `N_i − N_j ≥ w + L + 1`.** The interval `[N_j, N_i − w − 1]` has `N_i − N_j − w ≥ L + 1` integers. So some `t` in it
  has `T^{t+k_0}y ∈ {r_{k_0} = 1}` (uniform recurrence: every `L+1` consecutive times contain a visit). The component at
  `t + k_0 ≤ N_i − 1` is nonzero.
- **The other case** uses `[N_i + w, N_j − 1]`, with the component at `t + k_0 ≥ N_i`.
- Distinct `k` give distinct basis vectors, so no cancellation occurs.

**Lemma D.** This is B. H. Neumann's lemma (J. London Math. Soc. 29 (1954), 236–248, recalled, not re-read). The induction
on the number of distinct subgroups is correct: an `H_1`-coset avoiding the listed `H_1`-cosets is covered by the other
subgroups' cosets, and so is each translate.

**Lemma E.**
- `l = I + e_VE_12 + e_{V'}E_13` satisfies `l^2 = I` in characteristic 2, since `E_12E_13 = E_13E_12 = 0`.
- For `q = diag(a,b,c)`: `lq = q + e_VbE_12 + e_{V'}cE_13`, then
  `lql = q + (e_Vb + ae_V)E_12 + (e_{V'}c + ae_{V'})E_13`.
- `p ∈ lDl^{-1}` fixes the diagonal of `q` as that of `p`, and forces the stated entries.
- `V ↦ e_V` is a homomorphism from `(Clopen, Δ)` to `(R,+)` over `F_2`. So the bad pairs for `p` are empty or a coset of
  `ker φ_p × ker φ'_p`.
- Lemma D applies to the finite cover of `Clopen × Clopen` by the nonempty bad sets.

**Lemma F.**
- Units of `R` inside `LC(X,F_2)`: `e_Wg = 1` gives `1 − e_W = (1 − e_W)e_Wg = 0`.
- **(i)** For `a` with a coefficient `a_j` (`j ≠ 0`) equal to 1 on `O`:
  - the `u^j`-coefficient of `(1 + e_W)ae_W` is `a_j e_{T^jW∖W}`, and it vanishes on `ker φ` because `ae_W = e_Wb` there;
  - the points `z_i`, `T^{-j}z_i` (pairwise distinct) and the clopens `W_i` exist, since `O` is infinite and `T` has no
    periodic points;
  - every nonempty union `W_S` has `z_i ∈ T^jW_S∖W_S ∩ O`, so `S ↦ W_S` injects `F_2^{k+1}` into the quotient.
- **(ii)** `φ(W) = e_W(b − 1)` has a coefficient `e_Wβ_{m_0} ≠ 0` for every nonempty union of disjoint clopens inside
  `{β_{m_0} = 1}`.

**Assembly.**
- `g = lc` with `c = diag(u^{−K},1,u^K) ∈ EL_3(R)` (Whitehead in the `(1,3)` block). All pairwise differences are at least
  `K`.
- `g^{-1}Pg = c^{-1}Qc` avoids `S_y`, so `P ∩ gS_yg^{-1} = ∅`.

**Tower groups.**
- `π_y(e_{T^aW'}u^{a−b})δ_t ≠ 0` iff `T^{t−b}y ∈ W' ⊆ B`. So `t − b = τ_m`, and `t` and `t + a − b` both lie in
  `[τ_m, τ_m + h(W'))`, which is inside `[τ_m, τ_{m+1})`.
- `τ_0 = 0` is an endpoint, so the cut is preserved.

**Model tests.** A periodic `X` breaks Lemma F (i) and Lemma C (no uniform gap on a finite orbit with the needed freedom),
consistent with finite groups confining everything. The Fibonacci subshift satisfies all hypotheses.

## 5. Queue state
Served through line 4 of `sk/queue/sk-verify-13.txt`. Later lines go in part 2 and after.
