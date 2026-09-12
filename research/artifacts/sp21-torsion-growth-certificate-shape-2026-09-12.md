# Torsion growth along p-towers of Sp(n,1) lattices, and the shape of a Golod–Shafarevich certificate

Lane `hyperbolic-rf-torsion-growth`, 2026-09-12. This continues
`research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md`, whose Theorems A and B are
used by name below.

**Questions.**
1. What does growth of `H_1` torsion, along congruence towers and p-series
   towers of a cocompact arithmetic `Sp(n,1)` lattice, say about the open claim
   `sp21-lattice-pro-p-completions-have-finite-rank`?
2. Can the certificate of `sp21-golod-shafarevich-test-gives-infinite-pro-p-rank`
   ever fire?

## 0. Verdict

- **Neither side of the finite-rank claim is settled.**
- **Known about torsion growth: conjecture only.**
  - `δ(Sp(n,1)) = 0`. Bergeron–Venkatesh predict sub-exponential torsion in every
    degree along congruence towers, but their theorem needs `δ = 1`.
  - No source read proves a torsion-growth statement for `Sp(n,1)` lattices with
    trivial coefficients.
- **Theorem C (proved here).** Let `Δ <= Γ(p)` have uniform congruence closure of
  dimension `D`. Along the derived p-series of `Δ`:
  - `d_p >= D` at every level;
  - the pro-p congruence kernel is finite iff `d_p = D` from some level on;
  - in that case the p-part of `H_1` at level `i` has order at least
    `p^D·[Δ:D_i]/|N|`.

  Along the uniform congruence tower, the p-part of `H_1` always has order at
  least `p^D` times the index.
- **Theorem E (proved here).** Every continuous representation of `Δ̂_p` over a
  local field has finite image on the pro-p congruence kernel.
- **Theorem S (proved here; one import).** Where a certificate can live:
  - `d_p >= 5`, with `b_2 + d_p(tors H_2) < d_p²/4 - d_p`;
  - at a uniform level, either a large excess of `d_p` over `D`, or cup products
    of congruence characters that die in `H^2`;
  - a dying cup product already yields a non-congruence p-quotient.
- **Can a certificate exist at all?** No theorem found excludes one.
  - A certificate is a finitely presented Kazhdan group whose mod-p cohomology
    satisfies the *unweighted* Golod–Shafarevich inequality.
  - The homological strengthening of the Lubotzky–Zelmanov GS-τ conjecture
    (Lackenby, Conjecture 1.5) predicts that no such group exists.
  - The Kazhdan Golod–Shafarevich groups in the sources read satisfy only
    weighted inequalities.
  - Recorded as the open claim
    `kazhdan-group-with-golod-shafarevich-mod-p-cohomology`.

## 1. Sources

Read 2026-09-12 from the arXiv PDFs. They were downloaded and extracted with
`pdftotext` on MSI in `/projects/standard/hsiehph/sauer354/rf-torsion-lit`.

- **[BV] Bergeron–Venkatesh, arXiv:1004.1083, §1.2–1.4.**
  - Definition: "δ(G) to be the difference rank(G) − rank(K) ... It equals zero if
    and only if G has discrete series".
  - Conjecture 1.3: for `G` anisotropic over `Q` and congruence `Γ_N` with
    `∩_N Γ_N = {1}`, the limit of `log|H_j(Γ_N, M)_tors| / [Γ:Γ_N]` "exists for
    each j and is zero unless δ(S) = 1 and j = (dim(S)−1)/2".
  - Behaviour (1): "If δ = 0, then there is little torsion whereas
    H_j(Γ_N, M ⊗ Q) is large".
  - Theorem 1.4, the torsion lower bound for strongly acyclic `M`, assumes
    `δ(S) = 1`.
- **[7S] Abert–Bergeron–Biringer–Gelander–Nikolov–Raimbault–Samet,
  arXiv:1210.2961.**
  - Corollary 1.4: for a uniformly discrete sequence of uniform lattices with
    `Γ_n\X` BS-converging to `X`, `b_k(Γ_n)/vol(Γ_n\X) -> β_k^(2)(X)`.
  - `β_k^(2)(X)` is nonzero only for `k = dim X / 2`, and `χ(X^d) != 0` exactly
    when `δ(G) = 0`.
  - §8: L²-torsion is nonzero iff `δ(G) = 1`.
- **[AGN] Abert–Gelander–Nikolov, arXiv:1509.01711, abstract and Theorems 9–10.**
  Rank gradient and homology torsion growth vanish for right-angled lattices in
  higher rank simple Lie groups. `Sp(n,1)` has real rank one and is not covered.
- **[La] Lackenby, arXiv:math/0509036.**
  - Theorem 1.1: let `G` be finitely presented with a nested chain, each term
    normal of p-power index in the previous one, with linear growth of mod-p
    homology. Then `G` is large, or `G` has Property (τ) with respect to the chain.
  - Conjecture 1.5 (GS-τ Conjecture, attributed to Lubotzky and Zelmanov),
    verbatim: "Let G be a group with finite presentation ⟨X|R⟩, and let p be a
    prime. Suppose that d_p(G)²/4 > |R| − |X| + d_p(G). Then G does not have
    Property (τ) with respect to some infinite nested sequence {G_i} of normal
    subgroups with index a power of p."
- **[Er] Ershov, *Golod–Shafarevich groups: a survey*, arXiv:1206.0490.**
  - §1.3–1.4: Lubotzky (1983) observed that Golod–Shafarevich pro-p groups are
    not p-adic analytic.
  - §11: Serre's conjecture for `SL_2(C)` lattices is proved as three steps:
    (a) finite-index subgroups that are Golod–Shafarevich; (b) the congruence
    subgroup property makes pro-p completions analytic; (c) Golod–Shafarevich
    groups are not analytic.
  - §12: the groups `G_(p,d)` are Golod–Shafarevich for `p >= 3, d >= 9` and
    Kazhdan for `p > (d-1)²`. This is checked through the weighted series
    `1 - dτ + d(d-1)τ³ + dτ^p < 0` at `τ = 2/d`.
- **[EJ] Ershov–Jaikin-Zapirain, arXiv:1007.1489, §1.2.**
  - A pro-p group has positive weighted deficiency whenever `d(G) > 1` and
    `r(G) < d(G)²/4`.
  - Open subgroups of pro-p groups of positive weighted deficiency again have it.
  - "the smaller class of Golod-Shafarevich groups ... is not closed under
    operations (a) and (b)".
- **[AB] Ardakov–Brown, arXiv:math/0511345, §2–3.**
  - Completed group algebras of compact p-adic analytic groups are noetherian.
  - A compact group is p-adic analytic iff it has an open normal uniform pro-p
    subgroup.
  - For uniform `G`: `|G:P_2(G)| = |P_i(G):P_(i+1)(G)|`, and the dimension equals
    the minimal number of topological generators.
  - `F_p[[G]]` is a local ring with residue field `F_p`.

**Imported without re-reading.** These are book sources, and no arXiv copy was
located.
- **[DDMS]** Dixon–du Sautoy–Mann–Segal, *Analytic pro-p groups*. For uniform `U`
  and `i >= 0`, the lower p-series gives `P_(i+1)(U) = U^(p^i) = Φ^i(U)`, uniform
  of the same dimension. `[P_i, P_j] <= P_(i+j)` for the lower p-series of any
  pro-p group.
- **[Lz]** Lazard, *Groupes analytiques p-adiques* (1965), V.2.2.7: for `p` odd
  and `U` uniform, cup product gives `H^*(U;F_p) ≅ Λ^* H^1(U;F_p)`. Used only in
  Theorem S(iii) and in the congruence-tower remark of §3.
- **Standard facts on pro-p completions.**
  - A normal subgroup of p-power index has pro-p completion equal to its closure
    in the completion.
  - The derived p-series closes up to the Frattini series.
  - `H^1` of the completion equals `H^1` of the group, and `H^2` of the completion
    injects into `H^2` of the group.
  - The 5-term exact sequence holds for extensions of pro-p groups.
- **Strong approximation.** Used only to identify `D = 21·[k:Q]` for `Sp(2,1)`.

## 2. What is known about torsion growth for these lattices

**δ.** `G = Sp(n,1)` has complexification `Sp_(2n+2)(C)`, of rank `n+1`, and
`K = Sp(n) × Sp(1)` has rank `n+1`. So `δ(G) = 0`, and `X = H^n_H` has real
dimension `4n`.

1. **[BV] Conjecture 1.3 predicts little torsion.** Along every congruence tower
   with trivial intersection, and for every `j` and `M`,
   `log|H_j(Γ_N;M)_tors| = o([Γ:Γ_N])`. This is behaviour (1).
2. **[7S] Corollary 1.4 makes `b_k` sublinear for `k != 2n`.** In particular
   `b_2(Γ_N)/[Γ:Γ_N] -> 0` for `n >= 2`.
3. **No theorem for trivial coefficients.** The theorems in the sources read cover
   `δ = 1` [BV], or higher-rank right-angled lattices [AGN]. None proves a
   torsion-growth statement for `Sp(n,1)` lattices with trivial coefficients.
4. **Elementary linear upper bound; not new.**
   - Let `⟨X|R⟩` present `Γ` with relators of length `<= ℓ`. A subgroup `Δ` of
     index `n` has a Reidemeister–Schreier presentation with `n(|X|-1)+1`
     generators and `n|R|` relators.
   - `H_1(Δ;Z)` is finite by (T). It is the cokernel of an integer matrix of full
     column rank whose rows have `ℓ^1`-norm `<= ℓ`.
   - Hadamard's inequality on a nonzero maximal minor gives
     `|H_1(Δ;Z)| <= ℓ^(n(|X|-1)+1)`.

**Why growth rates cannot decide the certificate.**
- By Theorem S(i), `H_1` torsion feeds both `d_p` and `dim H^2(-;F_p)`. The
  certificate needs `b_2 + d_p(tors H_2) < d_p²/4 - d_p` on ONE cover.
- The rates `o(index)` [BV] and `O(index)` (item 4) say nothing about a single
  cover.
- So the certificate is decided only by a computation on one cover, or by a
  structural obstruction. §5–6 record the structural side.

## 3. Theorem C: mod-p homology along the derived p-series

**Setting.**
- `Γ`, `k`, `O`, `G` and `Γ(p)` are as in
  `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`.
- `Δ <= Γ(p)` has finite index, with closure `U = Δ̄_p` in `∏_(v|p) G(O_v)`, and
  `U` is **uniform** of dimension `D`.
- Every finite-index `Δ <= Γ(p)` has such a subgroup: by [AB], `Δ̄_p` has an open
  normal uniform subgroup `U'`, and `Δ ∩ U'` is normal of p-power index with
  closure `U'`.
- `P = Δ̂_p`, `π: P ->> U`, and `N = ker π` is the pro-p congruence kernel.
- `D_0 = Δ` and `D_(i+1) = [D_i, D_i] D_i^p` is the derived p-series.
- `U_i = U^(p^i)`, and `Δ_m = Δ ∩ U_m` is the uniform congruence tower.
- For `Sp(2,1)`, strong approximation makes `U` open in `∏_(v|p) G(O_v)`, so
  `D = 21·[k:Q]`.

**Theorem C.**
- **(a)** `d_p(D_i) >= D` for every `i`.
- **(b)** `N` is finite iff `d_p(D_i) = D` for all sufficiently large `i`. If `N`
  is infinite, then `d_p(D_i) > D` for infinitely many `i`.
- **(c)** If `N` is finite, then for all large `i`:
  - `[Δ:D_i] = |N|·p^(Di)`;
  - `H_1(D_i;Z)_(p) ≅ U_i^ab`, of order `>= p^(D(i+1)) = p^D·[Δ:D_i]/|N|`.
- **(d)** Unconditionally:
  - `|H_1(D_i;Z)_(p)| >= p^(D(i+1))` for every `i`;
  - along the congruence tower, with `P_m = π^(-1)(U_m)`,

    ```text
    p^D·[Δ:Δ_m]  <=  |U_m^ab|  <=  |H_1(Δ_m;Z)_(p)|  <=  |U_m^ab| · |N / closure[N, P_m]|.
    ```

**Proof.**

*Step 0 (translation).*
- `D_i` is normal of p-power index in `Δ`. Its pro-p completion is its closure in
  `P`, which is `Φ^i(P)`. So `d_p(D_i) = d(Φ^i(P))`.
- By (T), `H_1(D_i;Z)` is finite, so its p-part is `Φ^i(P)^ab`.
- `π` maps `Φ^i(P)` onto `Φ^i(U) = U_i` [DDMS]. Put `N_i = N ∩ Φ^i(P)`.
- `∩_i Φ^i(P) = 1`, because `P` is a finitely generated pro-p group.

*(a)* The surjection `Φ^i(P) ->> U_i` gives `d(Φ^i(P)) >= d(U_i) = D`, since `U_i`
is uniform of dimension `D` [DDMS, AB].

*(b), ⇒.* The `N_i` are decreasing finite subgroups with trivial intersection, so
`N_i = 1` for `i >= i_0`. Then `π` restricts to an isomorphism
`Φ^i(P) -> U_i`, and `d_p(D_i) = D`.

*(b), ⇐.* Suppose `d_p(D_i) = D` for all `i >= i_0`.
1. For such `i`, `Φ^i(P) ->> U_i` induces a surjection between Frattini quotients,
   both of dimension `D`. So it is an isomorphism
   `Φ^i(P)/Φ^(i+1)(P) -> U_i/U_(i+1)`.
2. Its kernel is `(π^(-1)(U_(i+1)) ∩ Φ^i(P)) / Φ^(i+1)(P)`, so
   `π^(-1)(U_(i+1)) ∩ Φ^i(P) = Φ^(i+1)(P)`.
3. `N_i` lies in the left-hand side, so `N_i <= N_(i+1)`. Hence `N_i = N_(i+1)` for
   all `i >= i_0`, and `N_(i_0) = ∩_i N_i = 1`.
4. So `N` embeds in the finite group `P/Φ^(i_0)(P)`.

If `N` is infinite, `d_p(D_i) = D` cannot hold for all large `i`. With (a), this
gives `d_p(D_i) > D` for infinitely many `i`.

*(c)* With `N_i = 1`:
- `π^(-1)(U_i) = Φ^i(P)·N` with trivial intersection. So
  `[Δ:D_i] = [P:Φ^i(P)] = [U:U_i]·|N| = p^(Di)·|N|`.
- `Φ^i(P) ≅ U_i` gives `H_1(D_i;Z)_(p) ≅ U_i^ab`.
- For the order, `U_i = P_(i+1)(U)` and
  `[P_(i+1), P_(i+1)] <= P_(2i+2) = U_(2i+1)` [DDMS]. So `U_i^ab` maps onto
  `U_i/U_(2i+1)`, of order `p^(D(i+1))` [AB].

*(d)*
- **Derived series.** `Φ^i(P)^ab ->> U_i^ab ->> U_i/U_(2i+1)`.
- **Congruence tower.**
  - `Δ_m` is normal of p-power index, with completion `P_m`.
  - The exact sequence `N/closure[N,P_m] -> P_m^ab -> U_m^ab -> 1` gives the upper
    bound.
  - The lower bound is the same commutator estimate:
    `|U_m^ab| >= |U_m/U_(2m+1)| = p^(D(m+1))`, and `[Δ:Δ_m] = [U:U_m] = p^(Dm)`. ∎

**Remarks.**
- **Inputs.** Theorem C uses neither superrigidity nor Theorem A nor [Lz]. Its
  inputs are (T) (finite abelianizations), [DDMS] and [AB]. No novelty is claimed;
  (b) is a Frattini argument.
- **With Theorem A.** For `Δ <= Γ(p)` with uniform closure: `Δ̂_p` has finite rank
  iff `d_p(D_i(Δ)) = D` eventually. Refuting
  `sp21-lattice-pro-p-completions-have-finite-rank` at `Δ` is the same as excess
  `d_p` at infinitely many levels. No finite computation decides either side.
- **Consistency with (T).** Under a finite kernel, `d_p` along the derived
  p-series is eventually *constant*. That is the extreme sublinear regime allowed
  by `fpbs-lackenby-derived-p-series-largeness`.
- **Consistency with [BV].** The proved bounds are *lower* bounds of size
  `log[Δ:D_i]` for `log|H_1(D_i;Z)_(p)|`. They are far below the index, so they are
  compatible with the predicted `o(index)`.
  - A matching upper bound `|U_i^ab| <= p^(D(i+1)+c)` would follow from perfectness
    modulo `p` of the scaled Lie lattice, through the Lazard correspondence. It is
    not proved here, and none of the claims uses it.
- **Congruence tower remark: more imports, not a Cairn claim.**
  - `M = H_1(N;F_p)` is a finitely generated `F_p[[U]]`-module. This follows from
    Crowell's exact sequence
    `0 -> H_1(N;F_p) -> F_p[[U]] ⊗_(F_p[[P]]) I_P -> F_p[[U]] -> F_p -> 0` and
    noetherianity [AB].
  - Let `J_m` be the ideal generated by `g - 1`, `g ∈ U_m`. Then
    `J_(m+1) <= J_m²`, since `x^p - 1 = (x-1)^p` in characteristic `p`. Nakayama
    then makes `dim M/J_m M` strictly increasing while `M` is infinite.
  - The 5-term sequence gives
    `D + dim M_(U_m) - dim H_2(U_m;F_p) <= d_p(Δ_m) <= D + dim M_(U_m)`.
  - With [Lz] (`dim H_2 = C(D,2)`): `sup_m d_p(Δ_m) < ∞` iff `N` is topologically
    finitely generated.

## 4. Theorem E: the kernel is invisible to local linear representations

**Theorem E.** Let `Δ <= Γ(p)` have finite index, `P = Δ̂_p`, `π: P ->> Δ̄_p` and
`N = ker π`. For every local field `F` and continuous `ρ: P -> GL_m(F)`, `ρ(N)` is
finite.

**Proof.**
1. **`char F > 0`.** `ρ|_Δ` has finite image by
   `sp21-lattice-positive-characteristic-images-finite`, and `ρ(P)` is its closure.
2. **`F/Q_ℓ` finite, `ℓ != p`.** `ρ(P)` is compact, so conjugate into `GL_m(O_F)`.
   Its intersection with the open pro-ℓ congruence subgroup is pro-p and pro-ℓ,
   hence trivial. So `ρ(P)` is finite.
3. **`F/Q_p` finite.**
   - Let `P_2 <= Δ̄_p × ρ(P)` be the image of `(π, ρ)`. It is a finite-rank pro-p
     group containing `Δ` densely, with `pr_1: P_2 ->> Δ̄_p` extending the
     congruence map.
   - Steps 1–3 of the proof of Theorem A (⇒) use of `(Δ̂_p, π_Δ)` only three
     things: finite rank, density of `Δ`, and a continuous surjection onto `Δ̄_p`
     restricting to the identity on `Δ`. So they apply to `(P_2, pr_1)`:
     - the Lie algebra of an open uniform subgroup is perfect by (T);
     - it is semisimple by superrigidity and Raghunathan vanishing;
     - the kernel ideal vanishes.
   - So `ker(pr_1) = {(1, ρ(n))} ≅ ρ(N)` is finite. ∎

**Consequences.**
- An infinite `N` has no faithful continuous linear representation over a local
  field.
- An infinite pro-p congruence kernel is a *non-linear* phenomenon. A
  Golod–Shafarevich `Δ̂_p` cannot be detected through a local-field linear quotient
  of infinite rank, since every such quotient is congruence up to a finite group.
- **Remark (imports: closed subgroups of free pro-p groups are free; centralizers
  there are procyclic).** If `Δ̂_p` contains a free pro-p subgroup `F` of rank
  `>= 2`, e.g. by Zelmanov when it is Golod–Shafarevich:
  - `F ∩ N != 1`, because `F` has infinite rank and `Δ̄_p` has finite rank;
  - `F ∩ N` is free pro-p of rank `>= 2`, because a normal procyclic subgroup of
    `F` would force `[F,F]` to be procyclic.

## 5. Theorem S: the shape of a certificate

Put `d = d_p(Δ)` and `r = dim H^2(Δ;F_p)`. Theorem B's hypothesis is `d >= 2` and
`r < d²/4`.

1. **(i) Universal coefficients.**
   - By (T), `H_1(Δ;Z)` is finite. So `H^1(Δ;F_p) = Hom(H_1, F_p)` and
     `H^2(Δ;F_p) = Hom(H_2, F_p) ⊕ Ext(H_1, F_p)`.
   - Hence `r = d + b_2(Δ) + d_p(tors H_2(Δ;Z))`, and the certificate holds iff
     `b_2 + d_p(tors H_2) < d²/4 - d`. In particular `d >= 5`.
   - Along towers `b_2` is sublinear [7S], so it is no asymptotic obstruction. The
     binding quantities are p-torsion in `H_1` (which raises `d`) and in `H_2`
     (which raises `r`).
2. **(ii) Presentations.**
   - For any finite presentation `⟨X|R⟩`: `r <= |R| - |X| + d`. The presentation
     complex `K` is the 2-skeleton of a `K(Δ,1)`, so `H^2(Δ) -> H^2(K)` is
     injective, and `dim H^2(K;F_p) = χ(K) - 1 + d`.
   - So a presentation with `d²/4 > |R| - |X| + d` is a certificate. That is
     precisely the hypothesis of [La] Conjecture 1.5.
3. **(iii) Uniform levels ([Lz], `p` odd).**
   - Let `Δ <= Γ(p)` have uniform closure `U` of dimension `D`, and let
     `V = inf(H^1(U;F_p)) <= H^1(Δ;F_p)`, of dimension `D`.
   - Let `t = dim ker(Λ²V -> H^2(Δ;F_p))` (cup product), and `e = d - D`.
   - The composite `Λ²H^1(U) ≅ H^2(U) -> H^2(Δ)` has rank `C(D,2) - t`. So
     `r >= C(D,2) - t`, and a certificate needs `C(D,2) - t < (D+e)²/4`.
   - With `t = 0`, `d > sqrt(2D(D-1))`. For `Sp(2,1)` over a quadratic field
     (`D = 42`) that is `d >= 59`.
   - At deep derived levels of a finite kernel, `e = 0` (Theorem C). So a
     certificate needs an infinite kernel and either large excess or `t` of order
     `D²/4`.
4. **(iv) Dying congruence classes give non-congruence p-quotients (no import).**
   - Suppose `0 != c ∈ H^2(U;F_p)` inflates to zero on `Δ`. Write `c` as inflated
     from a finite quotient `U/W`, with extension `1 -> F_p -> E -> U/W -> 1`.
   - The pullback to `Δ` splits, so `Δ -> U/W` lifts to `Δ -> E`. The lift is onto:
     otherwise its image is a section and `c = 0`.
   - It does not factor through `U`, since otherwise `c` would split on `U`.
   - So `E` is a non-congruence p-quotient. This shows `N != 1`; it does not show
     `N` is infinite.

## 6. Can a certificate exist at all?

- **What a certificate is.** A certificate on an `Sp(n,1)` lattice subgroup is a
  finitely presented Kazhdan group `G` with `dim H^2(G;F_p) < d_p(G)²/4`. The open
  claim `kazhdan-group-with-golod-shafarevich-mod-p-cohomology` asks whether any
  such group exists.
- **[La] Conjecture 1.5 (Lubotzky–Zelmanov).** It predicts that no presentation of
  a Kazhdan group satisfies `d_p²/4 > |R| - |X| + d_p`, because (T) gives (τ) along
  every chain.
  - Its homological strengthening, "`dim H^2(G;F_p) < d_p(G)²/4` excludes (τ) along
    some p-chain", would make the open claim false. Then Theorem B never fires on
    any `Sp(n,1)` lattice.
  - A certificate whose `r` is realized by a presentation would refute Conjecture
    1.5 itself.
- **Known Kazhdan Golod–Shafarevich groups are weighted.** [Er] §12's `G_(p,d)` has
  `d` generators and `d²` relators, read off the weighted series
  `1 - dτ + d(d-1)τ³ + dτ^p`. So `|R| - |X| + d_p >= d² - d > d²/4`, and the
  presentation inequality fails. We did not determine `dim H^2(G_(p,d);F_p)`.
  [EJ] notes that the unweighted class is not closed under passing to open
  subgroups, while positive weighted deficiency is.
- **Contrast with `SL_2(C)` [Er §11].**
  - Closed hyperbolic 3-manifold groups have `dim H^2(-;F_p) = dim H^1(-;F_p)` by
    duality. So `d >= 5` is a certificate, and Lubotzky's linearity theorem
    supplies covers with unbounded `d`.
  - For `Sp(n,1)` the manifold has dimension `4n >= 8`, so duality pairs `H^2` with
    `H^(4n-2)`, not with `H^1`. (T) keeps `b_1 = 0`, so `d` comes from p-torsion
    alone.
- **Answer.**
  - Not excluded by any theorem found.
  - An `Sp(n,1)` certificate would be the first Kazhdan group with unweighted
    Golod–Shafarevich mod-p cohomology in the sources read, and it would contradict
    the homological form of Lubotzky–Zelmanov.
  - Proving that form, even for these lattices, would close off the certificate
    route to failure of the congruence subgroup property. It would not prove that
    property.

## 7. Cairn integration

**Established, each with a `-proof` route:**
- `sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel` (Theorem C (a)–(b));
- `sp21-congruence-tower-p-torsion-grows-at-least-linearly` (Theorem C (c)–(d));
- `sp21-pro-p-kernel-invisible-to-local-linear-reps` (Theorem E; its route requires
  `sp21-lattice-positive-characteristic-images-finite`);
- `sp21-gs-certificate-shape-at-uniform-levels` (Theorem S).

**Open:** `kazhdan-group-with-golod-shafarevich-mod-p-cohomology`.

**Updated:** the `## Attempts` of `sp21-lattice-pro-p-completions-have-finite-rank`.

No root changes status.
- `sp21-lattice-has-congruence-subgroup-property` and
  `sp21-lattice-pro-p-completions-have-finite-rank` remain OPEN.
- Theorem C is an equivalence, not a proof of either side.
