# SK review 7, part 3: the wave-8 queue (LEF envelopes, universal hosts, overgroups, towers, second family)

Lane `sk-verify-7`, 2026-09-13 ~20:30 CDT. Queue `sk/queue/sk-verify-7.txt`, entries 2–21. I re-derived every step
before reading the owners' justifications.

## 0. Verdicts

| # | Claim (owner) | Verdict |
|---|---|---|
| 19 | `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple` + route (sk-strong-6 §2) | PASS; duplicate note D1 |
| 10 | `lamplighter-host-is-limit-of-finite-simple-expanders` + `lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit` + routes (sk-strong-8) | PASS; duplicate note D1 |
| 20 | `approximation-classes-without-simple-kazhdan-members` (sk-strong-6 §3) | PASS |
| 21 | `simple-kazhdan-envelope-theorems-force-non-lef-hosts` (sk-strong-6 §4) | PASS, conditional on the imports named in §2 |
| 2 | `countable-lef-groups-embed-in-two-generator-lef-groups` (sk-universal-lef-host-b) | PASS |
| 3 | `countable-lef-groups-embed-in-simple-kazhdan-lef-groups` | PASS |
| 4 | `simple-kazhdan-lef-host-for-recursive-lef-groups` | PASS; note N6 |
| 5 | `no-countable-group-contains-all-fg-lef-groups` | PASS |
| 6 | `no-decidable-group-contains-every-fp-rf-group` (sk-wp-host) | PASS, conditional on `uniform-wp-bound-excludes-bh-universal-targets` |
| 7 | `recursive-lef-growth-hosts-miss-some-fp-rf-group` (sk-wp-host) | PASS, conditional on the KMS Thm 4.19 import |
| 8 | `groups-embed-in-derived-subgroup-of-half-line-overgroup` (sk-perfect-overgroup) | PASS |
| 9 | route `amenable-groups-embed-in-kazhdan-linear-sofic-via-half-line` | PASS for the new overgroup step; the remaining inputs keep their own status |
| 11 | `rotation-factor-subshifts-have-linear-cost-towers` (Theorem R1) | PASS |
| 12 | `rotation-factor-subshift-lef-growth-at-least-exp-r-squared` (Theorem R2) | PASS |
| 13 | `rauzy-walk-bounds-lef-growth-by-special-factors` (Theorem U) | PASS; Corollary U1 conditional on Cassaigne (recalled) |
| 14 | `one-hole-toeplitz-subshifts-have-linear-cost-towers` (Theorem T1) | PASS |
| 15 | `one-hole-toeplitz-lef-growth-at-least-exp-r-squared` (Theorem T2) | PASS |
| 16 | `car-bernoulli-crossed-product-is-lamplighter-ring` (sk-strong-5) | PASS (folklore) |
| 17 | `car-shift-el3-is-marked-limit-of-qubit-shift-sl-groups` + route | PASS |
| 18 | route `finite-simple-groups-converge-to-simple-kazhdan-via-car-shift` + `finite-simple-kazhdan-limits-need-not-be-simple` | PASS |

No FAIL, no GAP. Entry 1 (sk-simpler-onepage) is in part 2.

## 1. Limits of finite simple expanders (entries 10, 19)
Both lanes build the same view models, on `Y_n = F_2^{Q_n}` without the base point. I checked sk-strong-8's
Lemmas 1–3 and sk-strong-6 §2 (i)–(iv) against each other.

- **Partial group model.**
  - `ψ_n(cδ) = (φ_n)_*c · φ_n(δ)` acts by `y ↦ φ_n(δ)·y + (φ_n)_*c`.
  - Multiplicativity uses `(cδ)(c′δ′) = (c + δc′)δδ′` and `(φ_n)_*(δc′) = φ_n(δ)·(φ_n)_*c′`, i.e.
    `1_{φ_n(δh)} = φ_n(δ)·1_{φ_n(h)}` for large `n`. Checked.
- **Covariance (★).**
  - `U(g)D(f′)U(g)^{-1}δ_y = f′(x_{g^{-1}y})δ_y`, with `x_y = y∘φ_n`.
  - Letter `s`: `(φ_n(s)^{-1}·y)(φ_n(h)) = y(φ_n(s)φ_n(h)) = x_y(sh) = (s^{-1}x_y)(h)`.
  - Letter `a`: `(y+1_e)(φ_n(h)) = x_y(h) + [h=e]`, using injectivity on the window together with `e`, and `φ_n(e) = e`.
  - sk-strong-6's form: `ℓ^{-1} = (δ^{-1}, δ^{-1}f_1)`, and `(ℓ̂^{-1}y)(φ(w)) = y(φ(δw)) + f_2(w) = (ℓ^{-1}x_y)(w)`.
  - Checked.
- **Nonvanishing (Lemma 2).**
  - Pairs with `δ = δ′` differ on `supp(c+c′)` for every `x`.
  - Pairs with `δ ≠ δ′` get fresh witness coordinates `h ∉ supp c ∪ supp c′`, with `x(δ^{-1}h) = 0` and `x(δ′^{-1}h) = 1`. This is possible because `Δ` is infinite, and fresh choices keep the prescriptions consistent.
  - A legal `y` with `x_y|_{W_p} = p` exists because `φ_n` is injective on `W_p`.
  - By (★) the points `ψ_n(ℓ)y` are distinct and the coefficient at `δ_{ψ_n(ℓ_0)y}` is `f_{ℓ_0}(ℓ_0x_y) = 1`.
  - Checked. sk-strong-6's topological-freeness version (a point moved by the finite set `E`) is equivalent.
- **Onto `M_{2^{|Q_n|}}(F_2)` (Lemma 3).**
  - `U(q)D(p)U(q)^{-1}δ_y = y(q)δ_y`, and the coordinate functions separate `Y_n`, so all diagonal matrix units appear.
  - Conjugating the flip gives translation by `1_q`, so every `T_c` appears, and `E_{y,y′} = T_{y+y′}E_{y′,y′}`.
  - `φ_n(s^{-1}) = φ_n(s)^{-1}` for large `n`.
  - Checked.
- **Marked limit and expanders.**
  - `ρ_n` is onto, so the images of `e_ij(t)` generate `EL_3(M_N(F_2)) = SL_{3N}(F_2)`; the letters include `u_su_s^{-1}`, so `1` is in the generated ring.
  - Triviality of words transfers both ways by Lemmas 2–3.
  - `EL_3(F)` is Kazhdan (EJZ), and its quotients with compatible generators have a uniform spectral gap.
  - `N_n = 2^{|Q_n|} → ∞` because `|Q_n| ≥ |B_r|`.
  - Checked.
- **Characterization.**
  - (i)⇒(ii): the Ore overgroup (two PASSes), `ℓ ↦ diag(u_ℓ,1,1)`, then the above.
  - (ii)⇒(i): marked limits of finite groups are LEF, and LEF passes to subgroups.
  - Checked.
- **D1 (duplicate).**
  - sk-strong-6 lands `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple`; sk-strong-8 lands `lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit` plus the host claim `lamplighter-host-is-limit-of-finite-simple-expanders`.
  - They state the same theorem, and neither names the other in `distinct_from`.
  - Recommendation for the Cairn steward: keep sk-strong-8's pair as canonical (it splits the host theorem from the characterization) and make sk-strong-6's claim a subsumption, or add block `distinct_from` both ways.
- **For the note.** This strengthens rev3 §2's corollary at no new cost: "a finitely generated group is LEF iff it is a subgroup of an infinite simple Kazhdan group that is a marked limit of finite simple expanders `SL_N(F_2)`". It matches the rev2 title. The only text change is the finite models: use `F_2[F_2^{Q_n}]` (view models) in place of `F_2[F_2^{Q_n} × Q_n]`, since the base-point models generate only a proper commutant.

## 2. The envelope table (entries 20, 21)
- **§3.** Amenable plus (T) gives a finite group: almost invariant vectors in `ℓ^2(G)` plus (T) give an invariant vector, which is constant.
  - A nontrivial homomorphism from an infinite simple group is injective. So residually finite, residually amenable, residually solvable and locally residually finite classes contain no infinite simple Kazhdan group, and Env fails already at the trivial group.
  - Checked.
- **§4.** `Γ_p` is finitely presented and amenable, with a central element killed by every finite-dimensional unitary representation.
  - So it is not RF; finitely presented and not RF means not LEF.
  - Every class containing the amenable groups (sofic, hyperlinear, weakly sofic, `F_q`-linear sofic through `rank(I − P_π)`, initially subamenable, operator-MF) forces a non-LEF host.
  - Conditional on `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, `finitely-presented-lef-groups-are-residually-finite` and `amenable-implies-operator-mf` as imported on main.

## 3. Universal LEF hosts (entries 2–5)
- **Lemma A.**
  - The doubled regular permutations are even; Ore Thm 1 gives commutators in `Sym`.
  - The level conjugation `(b^{-n}ab^n)(x,i) = (τ_{i+n}(x), i)` holds with right-to-left composition.
  - **Isolation.** A nontrivial level `i` needs `i+p_j ≡ s′` and `i+q_j ≡ s` with `s, s′ ∈ P_k`, so `q_j − p_j ≡ s − s′ (mod 4^{k+1})`.
    - Both sides are below `4^k` in absolute value, so the congruence is an equality.
    - Differences of distinct powers of 2 are distinct (2-adic valuation).
    - So `s = q_j`, `s′ = p_j` and `i ≡ 0`.
  - Level `0` carries `[α_{j,k}, β_{j,k}] = π_k(γ_j)`, and the words `w_j` do not depend on `k`.
  - Subgroups of algebraic ultraproducts of finite groups are LEF.
  - Checked. `ι(γ_j) = w_j(a,b)` is a commutator, so `ι(Γ) ≤ [Δ,Δ]`.
- **Theorem B.** `Γ × Z` is LEF, then Lemma A, then `lef-groups-embed-in-simple-kazhdan-lef-groups` (three PASSes). Checked.
- **Theorem C.** Restricted direct sums of LEF groups are LEF; there are countably many recursive presentations. Checked.
  - **N6.** The example "every f.g. linear group" rests on f.g. linear groups being recursively presented, i.e. having solvable word problem (Rabin, Malcev). The node recalls this through `universal-simple-kazhdan-lef-groups-exist-proof`, and it is not re-read here.
- **Proposition D.** Continuum many `G_X` (reviewed) against countably many f.g. subgroups of a countable group. Checked.
- **For the note.** Theorem C replaces rev3's Wilson-based universal host paragraph by a statement that is stronger (it contains non-RF LEF groups such as `G_Y` with recursive language and `[[T]]′`) and needs no Wilson import. The cost is Lemma A (about 12 lines) against a one-line Wilson citation. That trade-off is main's call.

## 4. Decidable and recursively bounded hosts (entries 6, 7)
- **Theorem A.**
  - `t(n)` is computable because the algorithm is total on finitely many words.
  - Subgroups' word problems are in `F(t)` up to substitution, and KMS gives finitely presented RF groups outside `F(t)`.
  - PASS, conditional on `uniform-wp-bound-excludes-bh-universal-targets`.
- **Theorem B.**
  - Step 2: `L_Γ(r) ≤ L_U(Cr)` by restricting a partial model.
  - Step 3: `ρ_Γ(n) ≤ L_Γ(n)` for `n ≥ m`. The homomorphism `ψ` from the free group agrees with `φ` on the ball by induction on word length, kills relators of length `≤ n`, and one homomorphism separates all pairs.
  - Step 4: `ρ_Γ(n) ≤ h(Cn) ≤ h(n^2) = f(n) < ρ_Γ(n)` for `n ≥ max(m,C)`, with the same generating set throughout.
  - Step 6: LEF plus solvable word problem makes `L_U` computable by exhaustive search.
  - PASS, conditional on KMS Thm 4.19 as quoted.
  - The consequence that every Sturmian `G_X` misses some finitely presented RF group follows from the reviewed bound `L(r) ≤ 2^{9(8r+4)^2}`.
- **For the note.** If the universal host paragraph goes in, sk-wp-host's one clause ("such a group has unsolvable word problem") is correct. It needs the KMS bibitem.

## 5. The half-line overgroup (entries 8, 9)
- `σh_sσ^{-1} = c_{1,s}`, and `[σ,h_s] = c_{1,s}∘c_{0,s^{-1}}` acts by `s^{-1}` on level 0 and trivially elsewhere, so `δ_0(Γ) ≤ [C,C]`.
- `C = E ⋊ ⟨σ⟩`:
  - `E` is `σ`-invariant and contains the `h_s`;
  - telescoping products of `c_{n,γ}` give all of `E`;
  - `E = ⋃E_M` with `E_M ≅ Γ^{2M+1}`.
- The permanence properties (amenable, sofic by Elek–Szabó permanence, torsion-free, solvable) follow from finite powers, directed unions and extensions by `Z`.
- **Not RF for non-abelian `Γ`.** `b_N = σ^Nδ_0(b)σ^{-N}` commutes with `a_0`. In a finite quotient `σ^{|F|!}` dies, so `δ_0([a,b]) ≠ 1` lies in every finite-index normal subgroup.
- Checked.
- The route into `amenable-groups-embed-in-simple-kazhdan-linear-sofic` replaces the false double-swap step correctly. Its other inputs (GJS subflows, faithful rank models, linear-sofic projective EL, `perfect-groups-embed-in-crossed-product-elementary-groups`) keep their own review status; the Whitehead identity inside the last one is the one checked in part 2 §2.

## 6. Cheap towers (entries 11–15)
- **Lemma 5.** `e_{W(a,q)} = e_a + e_a·u^{-q}e_au^q` (char 2), then one commutator. The cost `5 + 48q` follows from Lemma 1 of the reviewed bounds artifact.
- **R1.**
  - `x_0 = a` gives `θ ∈ cl I`.
  - `x_q ≠ a` gives `θ+η_n ∉ int I`. There is no wrap because `|I| + η < 1`, so `π(W) ⊆ [β′−η, β′]` (case `η_n > 0`).
  - `W` is nonempty because `int J ⊆ int I` (`η < |I|`) and `θ+η ∉ cl I`.
  - No returns: both endpoints lie in `J`, so `‖tα‖ ≤ η`. Best approximation then forces `t = ±q_n`, and `(T^{-q}x)_q = x_0` or `(T^qx)_0 = x_q` gives the contradiction.
  - Checked.
- **R2.**
  - `q_n ≤ 2m < q_{n+1}` and `κ ≤ 5+96m`.
  - `20κ + 480m = 100 + 2400m`.
  - `d(d−1)/2 = 18m^2+15m+3`.
  - `m ≥ (r−2500)/2400`.
  - Checked.
- **U.**
  - A strongly connected digraph has an ear decomposition with `E − V` ears.
  - The covering closed walk has length at most `E + (E−V+1)(V−1)`, and its labels give a cyclic word with exactly `L_n(X)`.
  - `p(n) ≤ |A| + Sn`.
  - Checked. U1 is conditional on Cassaigne's theorem (recalled, not read).
- **T1.**
  - `W_k = ⨆_a W(a,p_k)`, so the cost multiplies by `|A|`.
  - Nonempty because `x` is not periodic.
  - A return meets the dense orbit at `T^sx`. Both `s` and `s−t` are non-periodic positions, hence `≡ h_k (mod p_k)`, so `p_k | t`.
  - Checked.
- **T2.**
  - `p_k ≤ ρp_{k−1} ≤ 2ρm`.
  - `20|A|(5+96ρm) + 480m = 100|A| + (1920ρ|A|+480)m`.
  - Checked.

## 7. Second family (entries 16–18)
- **Identification.**
  - `LC(2^{[−n,n]}) ⋊ H_n ≅ M_{2^{2n+1}}(F_2)`: functions on a finite set by a simply transitive group.
  - The windows nest, and their union is `B` (a finitely supported flip with a function of finitely many coordinates lies in a window).
  - `L = (⊕Z/2) ⋊ Z`, so `R ≅ B ⋊_σ Z`.
  - Checked; folklore.
- **Qubit models.**
  - `πι(x^{(t)})π^{-1} = ι(x^{(t+1)})`, so `φ_N` is multiplicative on bounded supports once `N > 2L+1`.
  - Onto `M_{2^N}(F_2)` through the translates of the site-0 generators.
  - **Injectivity for `N > 8L+4`.** The input basis vector has a marker 1 at `⌊N/2⌋` and zeros outside `[−2L,2L]` apart from it.
    - `π^j` moves the marker to distinct positions, so different `j` give basis vectors with distinct markers.
    - `ι(b_j)` acts on sites in `[−L,L]` only.
    - Varying the pattern finds a vector not killed by a nonzero `b_j`.
  - Checked.
- **Firewall.** `SL_3(F_p)` is simple for `p ≡ 2 (mod 3)`, since `μ_3(F_p)` is trivial.
  - Reduction mod `p` is eventually faithful on bounded words, and Dirichlet gives infinitely many such `p`.
  - `SL_3(Z)` is Kazhdan and not simple.
  - Checked.
- sk-strong-5's verdict (no strictly shorter complete proof) is consistent with the length table.

## 8. Scope
- **Not re-read at source:** Ore 1951, KMS Thm 4.19 (quoted verbatim by the owner), Elek–Szabó permanence, GJS, Cassaigne, Rabin/Malcev.
- **Not searched:** novelty of any item; that belongs to sk-lit-novelty-2.
