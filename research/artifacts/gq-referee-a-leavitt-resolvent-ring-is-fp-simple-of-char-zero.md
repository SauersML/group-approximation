# Referee report (gq-referee-a, proof-gap lens): the Leavitt resolvent ring

**Reviewed.** Read on origin/main at the coordinator's request.
- `leavitt-resolvent-ring-is-fp-simple-of-char-zero` and its route `-proof` (lane gq-ring-fp-simple,
  aaf4b1279).
- `fp-simple-ring-of-characteristic-zero-exists` with its equivalence proof.
- The inputs it uses: `leavitt-nekrashevych-completion-simplicity-criterion` via
  `-simplicity-proof` §§1–3, and `leavitt-nekrashevych-completion-embeds-and-is-fp` via
  `-embedding-proof` §§2–5.

**Verdict: PASS.** `R_L = Z<s_1,s_2,t_1,t_2,N,A | t_i s_j = δ_ij, s_1t_1 + s_2t_2 = 1, N s_1 = s_1(N+1),
N s_2 = 0, A(N+1) = 1 = (N+1)A>` is a finitely presented simple ring containing `Q` unitally, and
`GL_n(Q) ≤ [R_L^x, R_L^x]` meets the centre trivially. I found no gap. Priority and citations
were not checked; see §6.

## 1. Commutation, resolvents, and `Q ⊆ R` (proof §§1–2)

- **The expansion of `N`.** From `N = N(s_1t_1 + s_2t_2)` and `N s_2 = 0` we get `N = s_1(N+1)t_1`.
  - This gives `t_1 N = (N+1) t_1`, `NP = PN = N` and `NE = EN = 0`.
  - It also gives `(N+c) s_1 = s_1 (N+c+1)` and `t_1 (N+c) s_1 = N+c+1`.
- **`A_c = t_1 A_{c-1} s_1` is a two-sided inverse of `N+c`.** I checked both sides directly:
  - `A_c(N+c) = t_1 A_{c-1}(N+c-1) s_1 = 1`, using `s_1(N+c) = (N+c-1)s_1`;
  - `(N+c)A_c = t_1(N+c-1)A_{c-1}s_1 = 1`, using `(N+c)t_1 = t_1(N+c-1)`.

  The `A_c` commute with `N` and with each other, because they are inverses of commuting elements.
- **`u_m · m = 1`.** `(N+m)s_2 = m s_2` and `(N+1)s_1^{m-1} = s_1^{m-1}(N+m)` give
  `u_m m = t_2 t_1^{m-1} A (N+1) s_1^{m-1} s_2 = 1`. Since `m` is central, every positive integer is a
  unit, so `R` is a `Q`-algebra. By §4 the map `Q → R` is injective.

## 2. Point (i): `R ≅ O_ψ` (proof §3)

- **`B` and `ψ`.** `B = Q[N][(N+c)^{-1} : c ≥ 1]`. Poles sit only at negative integers, so
  `f(N+1) ∈ B` and `f(0) ∈ Q`.
  - `ψ(f) = diag(f(N+1), f(0))` is a unital `Q`-algebra homomorphism.
  - `ψ` is injective, since `f(N+1) = 0` forces `f = 0`.
- **`O_ψ → R`.**
  - `φ: Q[N] → R` is a `Q`-algebra map because `Q` is central in `R`. It extends to the
    localization `B`, because each `N+c` maps to the unit `N+c`, which commutes with `φ(Q[N])`.
  - `κ(b) = s_1 φ(b(N+1)) t_1 + s_2 φ(b(0)) t_2` is a unital ring homomorphism, since
    `t_i s_j = δ_ij`.
  - `κ` agrees with `φ` on `N` (`N = s_1(N+1)t_1`) and on `Q`. A homomorphism out of a localization
    is determined on `Q[N]`, so `κ = φ` on `B`. That is exactly covariance, so `O_ψ → R` is defined.
- **`R → O_ψ`.** The Leavitt relations are clear, and `A ↦ (N+1)^{-1}`. Covariance for `N` reads
  `N = s_1(N+1)t_1`, which gives `N s_1 = s_1(N+1)` and `N s_2 = 0`.
- **Composites.** `A ↦ (N+1)^{-1} ↦ A_1 = A`.
  - `(N+c)^{-1} ↦ A_c = t_1^{c-1} A s_1^{c-1} ↦ t_1^{c-1}(N+1)^{-1}s_1^{c-1}`.
  - This equals `(N+c)^{-1}` in `O_ψ`, since covariance gives `t_1 b s_1 = ψ(b)_{11} = b(N+1)`.
  - Ring maps between `Q`-algebras are `Q`-linear. So both composites are the identity.

## 3. Point (ii): ψ-minimality and aperiodicity (proof §§4–5)

- **ψ-minimality.** From `b ∈ I` saturation gives `b(N+1) ∈ I` and `b(0) ∈ I`. Iterating gives
  `b(k) ∈ I` for all `k ≥ 0`. A nonzero `b` has finitely many zeros, so `I` contains a unit of `Q`.
- **Level `L`.** `(s_a t_b) y` has coefficient `[μ = aμ''] Y_{bμ'', ν}`, while `y (s_a t_b)` has
  `[ν = b] Y_{μ a}`, and coefficients are unique.
  - `ν ≠ b` gives `Y_{bμ'',ν} = 0`.
  - `ν = b` gives `Y_{aμ'', a} = Y_{bμ'', b} =: w_{μ''}`.
  - So `y = Σ s_{νω} w_ω t_ν`.
- **Level `L + j`.** `ψ` is diagonal, so padding gives `Σ_u s_{νωu} ψ_u(w_ω) t_{νu}`. The triple
  `(ν, ω, u)` can be read off the index pair.
  - The level-`(L+j)` constraint says a coefficient at `(μ', ν')` vanishes unless `μ'` starts with
    `ν'`.
  - That means `ωu` starts with `u`, i.e. `u` is a prefix of `ω^∞`.
- **Evaluation at integers.** For `u = 1^a 2 x`, `ψ_u(w) = w(a)`: shift `a` times, evaluate at `0`,
  then constants are fixed. Only one of `1^a21` and `1^a22` can be a prefix of `ω^∞`.
  - So `w_ω(a) = 0` for all `a ≥ 0`, hence `w_ω = 0`.
- **Negative degrees.** The map `s_i ↔ t_i`, identity on `B`, respects covariance exactly because
  `ψ(b)` is symmetric; here it is diagonal. `B` is commutative, so this is an anti-automorphism
  that maps `C` onto `C` and `O_k` onto `O_{-k}`.

## 4. Point (iii): the criterion applies to a non-finitely-generated, localized `B`

- **Simplicity proof §§1–3.** It uses only covariance and injectivity of `ψ`:
  - normal form and uniqueness from `t_{μ'} s_μ = δ`;
  - graded ideals, through `O_ψ/<I> ≅ O_{ψ̄}` and injectivity of `B/I → O_{ψ̄}`;
  - the main direction: minimal support, shift the lowest degree to 0, `I_0 ∩ B` is saturated and
    nonzero, then `1 ∈ I_0` and aperiodicity.

  Nothing uses finite generation of `B` or finite-stateness of `ψ`.
- **Embedding proof §§2–5.** Injectivity of `B → O_ψ` comes from the direct limit
  `C = lim M_{2^n}(B)`, the isomorphism `Φ: C ≅ M_2(C)`, and the module `V ≅ V^{(2)}_Φ`. This too
  needs only that `ψ` is injective.
  - Only §1 (finite presentation of `O_ψ` from one of `B`) needs `B` finitely presented, and the
    route does not use it.
  - Finite presentation of `R_L` is its explicit 9-relation presentation, transported by §2.
- **Nonzero.** `R_L ≠ 0` because `B ↪ O_ψ`.

## 5. The final claims

- **Matrix rings.** `M_2(R) ≅ R` via `(x_ij) ↦ Σ s_i x_ij t_j`, so `M_n(R) ≅ R` for every `n`.
- **`GL_n(Q)` in the derived subgroup.** `g ↦ diag(g, det g^{-1}, 1)` puts `GL_n(Q)` inside
  `SL_{n+2}(Q)`, which is perfect and lies in `GL_{n+2}(R) ≅ R^x`. So `GL_n(Q) ≤ [R^x, R^x]`.
- **The centre.** An element central in `R^x` commutes with `SL_{n+2}(Q)`, so it is scalar in
  `M_{n+2}(Q)`. Its last diagonal entry is 1, so it is the identity.
- **The equivalence (a)–(c) of `fp-simple-ring-of-characteristic-zero-exists`.** If `p·1_R = 0`,
  then the image of `1` equals `p·r = (p·1_R) r = 0`. A simple ring has characteristic 0 or a prime.

## 6. Scope and what this does not give

- This is a ring theorem. It does not settle `G`: whether `[R_L^x, R_L^x]` modulo its centre is
  finitely presented and simple is open (`leavitt-resolvent-derived-units-mod-centre-fp-simple`).
  It also does not settle `G'`. A finitely presented group containing `GL_n(Q)` needs a separate
  argument, for instance finite presentation of `St_N(R_L)` together with the Steinberg embedding.
- **Priority is not checked here.** The claim "no source states existence of a finitely presented
  simple ring of characteristic zero" needs `gq-lit-arxiv` to search Bokut, Belyaev (1978),
  Kharlampovich–Sapir's survey of algorithmic problems in varieties, and the Dniester notebook.
- **Non-blocking wording.** The route cites `leavitt-nekrashevych-completion-embeds-and-is-fp` but
  uses only its part 2. Saying so in the route would prevent a reader from inferring finite
  presentation from part 1.
