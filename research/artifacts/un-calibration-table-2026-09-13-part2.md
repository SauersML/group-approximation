# UN calibration table, part 2 of 2: the table and ring-by-ring notes

Lane `un-calibration`, 2026-09-13. Status: **unreviewed**. Lemmas L1–L8 are in part 1
(`research/artifacts/un-calibration-table-2026-09-13-part1.md`). "unknown" means neither proved here nor quoted.

**L9 (faithful rank function ⇒ `[1]` finite).** If `R` has a faithful Sylvester matrix rank function, then `R ≅ R ⊕ P` forces `P = 0`.
*Proof.* Isomorphic idempotents `e = ab`, `e' = ba` (with `a = eae'`, `b = e'be`) satisfy `rk(e) = rk(abab) <= rk(ba) = rk(e')`, and the
reverse inequality holds by symmetry. So `R ≅ R ⊕ P`, with `P` the image of an idempotent matrix `f`, gives `1 = rk(1) = 1 + rk(f)`
by (S3). So `rk(f) = 0`. Every entry of `f` then has rank 0, so `f = 0` by faithfulness. ∎

## 1. The table

Columns: fg = finitely generated as a ring; DF / SF = directly / stably finite; rank = Sylvester matrix rank functions; LEF ring =
matricial over finite fields, "/ k" = matricial over the base field; `EL_n` = the elementary group, `n >= 3` unless stated.

| # | ring `R` | fg | simple | DF | SF | `V(R)` at `[1]` | rank | LEF ring / over k | `EL_n(R)` |
|---|---|---|---|---|---|---|---|---|---|
| 1 | `F_q` | yes | yes | yes | yes | finite | faithful | yes / yes | finite: (T), LEF, MF, sofic |
| 2 | `F_q[t]` | yes | no | yes | yes | finite | faithful | yes / yes | (T), LEF, MF, sofic |
| 3 | `F_q[t,t^(-1)]` | yes | no | yes | yes | finite | faithful | yes / yes | (T), LEF, MF, sofic |
| 4 | `M_2(F_q[t])` | yes | no | yes | yes | finite | faithful | yes / yes | (T), LEF, MF, sofic |
| 5 | `LC(X,F_q)⋊Z`, `X` Fibonacci | yes | yes | yes | yes | finite | faithful | yes / yes | (T), simple mod centre, LEF, MF, sofic |
| 6 | `LC(Z_2,F_q)⋊Z`, odometer | **no** | yes | yes | yes | finite | faithful | yes / yes | **not fg, no (T)**; LEF, MF, sofic |
| 7 | `LC(Ω_U,F_q)⋊Z^2`, Labbé | yes | yes | yes | yes | finite | faithful (rank-metric) | unknown / unknown | (T), simple mod centre, `F_q`-linear sofic; LEF, MF, sofic unknown |
| 8 | `L_(F_q)(1,2)` | yes | yes | no | no | paradoxical, `[1]=2[1]` | none | no / no | (T), no nontrivial MF quotient, simple mod centre; sofic unknown |
| 9 | `L_(F_q)(1,3)` | yes | yes | no | no | paradoxical, `[1]=3[1]` | none | no / no | (T), no nontrivial MF quotient, simple mod centre; sofic unknown |
| 10 | Cohn ring `𝒞` | yes | no | no | no | paradoxical | none | no / no | (T), no nontrivial MF quotient (`n >= 2`) |
| 11 | Toeplitz `J = F_2⟨s,t | ts=1⟩` | yes | no | no | no | infinite, not paradoxical | some, none faithful | no / no | (T); not MF (`n >= 4`); nontrivial MF quotient; sofic unknown |
| 12 | Weyl `A_1(F_p)` | yes | no | yes | yes | finite | faithful | yes / yes | (T), LEF, MF, sofic |
| 13 | Weyl `A_1(Q)` | **no** | yes | yes | yes | finite | faithful | **yes / no** | not fg, no (T); LEF, MF, sofic |
| 14 | `F_q[Γ]`, `Γ` fg LEF (e.g. residually finite), `Γ != 1` | yes | no | yes | yes | finite | faithful | yes / yes | (T), LEF, MF, sofic |
| 15 | `F_q[Γ]`, `Γ` fg amenable, not LEF | yes | no | yes | yes | finite | faithful (rank-metric) | **no / no** | (T), **not LEF**, `F_q`-linear sofic; MF, sofic unknown |
| 16 | simple, DF, not SF (existence unknown) | – | yes | yes | no | – | none | no / no | no nontrivial MF quotient at rank `>= 2n` |

## 2. Notes and proofs

**Rows 1–4.**
- **fg.** Clear: `F_q = F_p[primitive element]`; `t`, `t^(-1)`; matrix units.
- **Not simple (rows 2–4).** The ideals `(t)`, `(t − 1)` and `M_2(tF_q[t])` are proper and nonzero.
- **LEF ring.**
  - Row 2: `F_q[t] → F_q[t]/(t^N)`, acting on itself, is an exact homomorphism into `M_N(F_q)`. It is injective on polynomials of
    degree `< N`.
  - Row 3: `F_q[t^(±1)] → F_q[Z/N]`. A nonzero `t^(−m)p(t)` with `deg p = d` survives once `N > d`, because `t^N − 1` cannot divide `p`.
  - Row 4: `M_2` of the row-2 embedding.
- **Consequences.** SF, a faithful rank function and a finite `[1]` follow from L1, L2 (faithfulness: separated translates, as in row 14,
  or `rank >= 1` in the fixed coordinates) and L9. (T) follows from L7. LEF, MF and sofic follow from L4.

**Row 5 (the Pestov ring).**
- **fg, simple, LEF ring.** Quoted from `minimal-subshift-algebra-is-simple-lef-ring`: "`R` is generated as a ring by `u`, `u^(-1)`, the
  letter cylinders `chi_[x_0=a]`, and, when `q` is not prime, a primitive element of `F_q`"; "`R` is simple, with centre `F_q`"; "`R` is LEF
  as a ring. There is an injective unital `F_q`-linear ring homomorphism `R -> prod_omega M_(N_k)(F_q)`".
- **`EL_n`, every `n >= 3`.** Quoted from `free-minimal-subshift-elementary-groups-are-simple-kazhdan`: "Every normal subgroup of `G_n` is
  central or all of `G_n`" and "`S_n = G_n/Z(G_n)` is an infinite simple group with property (T)".
- **Consequences.** LEF, MF and sofic by L4; SF, faithful rank and finite `[1]` by L1, L2, L9.

**Row 6 (odometer).** `X = Z_2` with `Tx = x + 1`; `R = LC(Z_2, F_q) ⋊ Z`. Node `odometer-crossed-product-elementary-groups-not-kazhdan`.
- **Not fg.**
  - Let `S_M` be the set of finite sums `Σ f_j u^j` with every `f_j` constant on the cosets of `2^M Z_2`.
  - `S_M` is a unital subring. `u f u^(-1) = f∘T^(-1)` is again constant on these cosets, and so are products.
  - `S_M ⊊ S_(M+1)`: `χ_(2^(M+1) Z_2) ∉ S_M`, by uniqueness of the normal form.
  - Every finite subset of `R` lies in some `S_M`, and `R = ∪_M S_M`. So `R` is not finitely generated.
- **Simple.** The proof of §1.3 of the Pestov artifact uses only `T^j x != x` (`j != 0`) and minimality. Both hold here: `x + j != x` in
  `Z_2`, and every orbit `x + Z` is dense. Alternatively, `steinberg-algebra-simple-iff-minimal-effective`.
- **LEF ring.**
  - For `K >= M`, `S_M` acts on `F_q^(Z/2^K)` by `f δ_c = f(c) δ_c` and `u δ_c = δ_(c+1)`. This is an exact homomorphism `ρ_K`,
    because `LC(Z/2^M)` pulls back along `Z/2^K → Z/2^M` equivariantly.
  - Put `ρ(x) = [ρ_K(x)]_K`, with `ρ_K(x) := 0` while `K <` the level of `x`. Then `ρ` is a unital ring homomorphism into
    `∏_ω M_(2^K)(F_q)`.
  - It is injective: if `0 != x = Σ_(|j|<=d) f_j u^j`, the vectors `δ_(c+j)` are distinct once `2^K > 2d`, so `ρ_K(x) != 0`.
- **`EL_n` (`n >= 2`).**
  - `EL_n(R) = ∪_M EL_n(S_M)`, a strictly increasing union: `e_12(χ_(2^(M+1) Z_2)) ∉ M_n(S_M)`. So `EL_n(R)` is not finitely generated.
  - It has no (T), by L7.
  - It is LEF, MF and sofic, by L4.
- **Firewall.** Exact tower models and simplicity do not make Kazhdan groups. The finite generation that EJZ needs comes from
  expansiveness (subshifts), not from towers.

**Row 7 (Labbé).** `Ω_U` is Labbé's 19-tile minimal aperiodic Wang shift. It is free minimal as recorded on main: the Labbé nodes apply
`zd-derived-full-group-fp-forces-quantum-rigidity`, stated for "a free minimal subshift of finite type". This was not re-derived here.
- **fg.** As in row 5: `u_1^(±1)`, `u_2^(±1)`, the letter cylinders, and a primitive element. Shifted letters generate all cylinders.
- **Simple, faithful Følner rank model.** Quoted from `free-minimal-crossed-products-are-simple-with-rank-models`: "`R` is simple,
  `Z(R) = k`" and "Truncating the orbit representation to boxes `[0, n)^d` gives unital rank-approximate homomorphisms".
- **`EL_n`.** Quoted from `free-minimal-subshift-elementary-groups-are-simple-kazhdan`: "`S_n = G_n/Z(G_n)` is an infinite simple group
  with property (T), and it is `F_q`-linear sofic".
- **Soficity.** `free-minimal-subshift-elementary-groups-are-sofic` is OPEN, and its Attempts record that "The periodic-model LEF
  mechanism" is unavailable for SFTs without periodic points.
- **LEF ring.** Unknown. An exact local model must represent the finitely many tile relations with exactly commuting shifted letter
  idempotents on windows. This is related to, but not the same as, `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`.
- **Consequences.** SF by L2 and finite `[1]` by L9.

**Rows 8–9 (Leavitt over `F_q`).**
- **fg.** `s_i`, `t_i` and a primitive element.
- **Simple, and `EL_n` simple mod centre.** Quoted from `steinberg-elementary-groups-are-simple-mod-centre`, whose calibrating cases
  include "`L_k(1,d) = A_k(𝒢_d)`, with `𝒢_d` the Cuntz groupoid", together with `steinberg-algebra-simple-iff-minimal-effective`.
- **Not DF.** Quoted from tex Cor l.1016 proof: "take $s=s_1$ and $t=t_1$; then $1-s_1t_1=\sum_{i\ge2}s_it_i$ and
  \[ t_2(1-s_1t_1)s_2=1." So `1 − s_1 t_1 != 0`.
- **`[1] = d[1]`.** Quoted from tex l.1301–1302: "The maps $x\mapsto(t_1x,\dots,t_dx)$ and $(y_1,\dots,y_d)\mapsto\sum_is_iy_i$ are
  mutually inverse isomorphisms of right $R$-modules between $R$ and $R^d$".
- **No rank function.** L3 with `C = (s_1 s_2)` and `D = (t_1 t_2)^T`, since `t_i s_j = δ_ij`.
- **Not a LEF ring.** It is not SF, so L1 rules it out.
- **`EL_n`.** No nontrivial MF quotient, by tex Cor l.1016, quoted in part 1 L8. So it is not MF, and not LEF by L4. (T) by L7.
  Soficity: unknown.

**Row 10 (Cohn ring).** Quoted from tex l.217: "$\mathcal C=\mathbb Z\langle s_0,s_1,t_0,t_1\rangle/(t_is_j-\delta_{ij}:i,j\in\{0,1\})$".
- **Not DF.** Quoted from tex l.936–937: "In $\mathcal C$ put $s=s_0$, $t=t_0$, and $e=1-st$. Then $ts=1$, $e^2=e$, $es=te=0$, and
  $t_1es_1=1$". So `e != 0`.
- **Not simple.** The relations `t_i s_j = δ_ij` hold in `L_Q(1,2)`. That algebra is nonzero: it acts faithfully on locally constant
  functions on `{0,1}^N` (`depth-monotone-leavitt-subalgebras-are-stably-finite`, proof sketch). So `2 != 0` in `𝒞`. On the other hand
  `𝒞/2𝒞` maps onto `L_(F_2)(1,2) != 0` (tex l.939: "since it maps onto $L_{\F_2}(1,2)$"). So `2𝒞` is a proper nonzero ideal.
- **Paradoxical.** L3 with `C = (s_0, e s_1)` and `D = (t_0, t_1 e)^T`: `DC = [[t_0 s_0, t_0 e s_1], [t_1 e s_0, t_1 e s_1]] = I_2`, using
  `te = es = 0` and `e² = e`. So there is no rank function, and it is not a LEF ring (L1).
- **`EL_n`.** Thm l.918 applies, since `R(1 − st)R ∋ t_1 e s_1 = 1`. Every homomorphism from `EL_n(𝒞)`, `n >= 2`, to an MF group is
  trivial. (T) for `n >= 3` by L7.

**Row 11 (Toeplitz–Jacobson).** Quoted from tex l.1122–1125: "The Toeplitz--Jacobson algebra $J=\F_2\langle s,t\mid ts=1\rangle$ has
$1-st\ne0$ of order two, while $J/J(1-st)J\cong\F_2[z,z^{-1}]\ne0$, so $1-st$ is not full ... Proposition~\ref{prop:torsion-defect-ring}
shows that $\EL_n(J)$ is not MF for $n\ge4$".
- **`V(R)` at `[1]`.** `[1] = [st] + [e]` and `st ~ ts = 1`, so `[1] = [1] + [e]` with `e != 0`: infinite. The quotient
  `J → F_2[z^(±1)]` pulls back a rank function, so `[1]` is not paradoxical (L3).
- **No faithful rank function.** `rk(e) = rk(1) − rk(st) = 0` (L2 complementary idempotents, L9 equivalence), while `e != 0`.
- **MF radical.** Quoted from tex l.1143–1148: "the quotient $\EL_n(\F_2[z,z^{-1}])$ is residually finite, so MF, and
  \[ \Rad_{\mathrm{MF}}(\EL_n(J))=\EL_n(J,JeJ)\cong\bigcup_N\mathrm{SL}_N(\F_2) \qquad(n\ge4)," So `EL_n(J)` has a nontrivial MF
  quotient and is not MF.
- **Other entries.** Not LEF (L4). (T) for `n >= 3` (L7). Soficity: unknown. The kernel is locally finite and the quotient residually
  finite, but "amenable-by-sofic ⇒ sofic" is not quoted here.

**Row 12 (`A_1(F_p) = F_p⟨x, y⟩/(xy − yx − 1)`).** Uses the standard PBW basis `x^i y^j`, recalled, not quoted.
- **Not simple.** `x^p` is central (`[y, x^p] = p x^(p−1) = 0`). The representation `x ↦ x`, `y ↦ −d/dx` on `F_p[x]/(x^p)` kills
  `x^p` and is nonzero, so `(x^p)` is a proper nonzero ideal.
- **Representations.** For a finite field `F ⊇ F_p` and `a, b ∈ F`, let `ρ_(a,b)` act on `V = F[x]/(x^p − a)` by `x ↦ x` and
  `y ↦ c − d/dx`, where `c^p = b`.
  - `d/dx` is well defined, since `d/dx(x^p − a) = 0`, and `(d/dx)^p = 0` on `V`. So `ρ_(a,b)(x^p) = a` and `ρ_(a,b)(y^p) = b`.
  - Independence: `{x^i (d/dx)^j : i, j < p}` is linearly independent in `End(V)`. Take the least `j_0` with some `c_(i j_0) != 0`
    and apply the sum to `x^(j_0)`. This gives `Σ_i c_(i j_0) j_0! x^i = 0` with `i < p`, a contradiction.
  - Writing `z = Σ_(i,j<p) c_ij(x^p, y^p) x^i y^j`, we get `ρ_(a,b)(z) != 0` iff some `c_ij(a, b) != 0`.
- **LEF ring.** Given finitely many nonzero `z`, choose `(a, b) ∈ F_(p^m)^2`, `m` large, where the product of chosen nonzero
  coefficients does not vanish. These sets have the finite intersection property, so an ultrafilter exists. `F_(p^m) ⊆ M_m(F_p)`
  gives matricial over `F_p`. Ranks are at least `1/p` normalized, so the rank function is faithful.
- **Consequences.** SF by L1 and L2; (T) by L7; LEF, MF and sofic by L4.

**Row 13 (`A_1(Q)`).** Node `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q`.
- **Simple.** In characteristic 0, `ad_y(x^i) = −i x^(i−1)` and `ad_x(y^j) = j y^(j−1)`. Starting from a nonzero element of an
  ideal, commutators reach a nonzero scalar.
- **DF.** It is a domain (leading terms).
- **Not matricial over any characteristic-0 field.** An exact model of `{x, y, xy, yx, 1}` in `M_N(k)` gives
  `0 = tr(ρ(x)ρ(y) − ρ(y)ρ(x)) = N`, which fails in characteristic 0.
- **LEF ring over the primes.** For a finite set in `A_1(Q)`, all coefficients lie in `Z_(p)` for all but finitely many `p`. The ring
  homomorphism `A_1(Z_(p)) → A_1(F_p) → End(F_p[x]/(x^p))`, `y ↦ −d/dx`, is exact. By row 12's independence argument, `z != 0` of
  degrees `< p` with a coefficient not divisible by `p` maps to a nonzero matrix. So `A_1(Q) ↪ ∏_ω M_p(F_p)`.
- **Not fg as a ring.** Finitely many elements have coefficients in `Z[1/m]`, which misses `1/p` for `p ∤ m`. Likewise
  `EL_n(A_1(Q)) = ∪_m EL_n(A_1(Z[1/m]))` is strictly increasing, so it is not finitely generated and has no (T) (L7).
- **Consequences.** SF (L1), faithful rank (L2), finite `[1]` (L9); LEF, MF and sofic (L4).

**Rows 14–15 (group rings).** Node `group-ring-lef-iff-group-lef-iff-elementary-group-lef`, which is L5.
- **Not simple.** The augmentation ideal is proper and nonzero when `Γ != 1`.
- **Faithful rank functions.**
  - Row 14: `ρ_i(x) = Σ a_g λ(σ_i(g))`. Right translates `λ(·)δ_q` with disjoint supports `σ_i(S) q`, where `S = supp x`, give
    `rank >= |Q_i| / |S|^2`.
  - Row 15: truncate left multiplication to Følner sets `B_n`. The same separated-translates count gives `rank >= |B_n|/|S|^2 − o(|B_n|)`,
    and truncation is multiplicative up to `o(|B_n|)`.
- **Row 15.**
  - SF by L2 with faithfulness in place of simplicity.
  - Not a LEF ring and `EL_n` not LEF, by L5.
  - `EL_n` is `F_q`-linear sofic: units inject into the rank-metric ultraproduct with `rk(g − h) > 0`.
  - Examples: a finitely presented amenable group that is not residually finite is not LEF. "finitely presented and LEF imply residually
    finite" is recorded in `labbe-shift-derived-full-group-is-lef`, citing Grigorchuk–Medynets. Existence of such groups (e.g. Abels'
    groups) is recalled, not quoted.

**Row 16.** If `R` is simple and SF fails, some `M_n(R)` is not DF. Quoted from `stably-infinite-ring-elementary-groups-have-no-mf-quotient`,
Corollary: "If `R` is countable, simple and unital but not stably finite, and `M_n(R)` is not directly finite, then every homomorphism
from `EL_N(R)` to an MF group is trivial for every `N >= 2n`." There is no rank function (L2) and no LEF-ring model (L1). A countable
simple unital ring that is DF but not SF: existence unknown here. Rørdam's C*-algebra with a finite and an infinite projection is
recalled, not verified, and is not a countable ring.

## 3. What the table says about U1–U4 (remarks, unreviewed)

- **F1 (U2, U3: the matricial notion).** Row 13. `A_1(Q)` is simple, SF and has a faithful rank function. It is not matricial over its
  base field, or over any characteristic-0 field, yet `EL_n(A_1(Q))` is LEF. The right ring condition is the LEF ring, with matrix
  ultraproducts over varying finite fields, not "embeds in `∏_ω M_N(k)`" over the base field.
- **F2 (U2, finite generation).** Row 6. Towers plus simplicity give LEF, not (T). Kazhdan families need finitely generated rings,
  i.e. expansive systems.
- **F3 (U2, exact versus rank-metric models).** Row 15. A faithful rank-metric Sylvester rank function and stable finiteness do NOT make
  `EL_n` LEF: `EL_n(F_q[Γ])` is (T), linear sofic and not LEF when `Γ` is amenable and not LEF. Exact (LEF-ring) models are needed. Row 7
  is the simple-ring case where only the rank-metric model is known.
- **F4 (U1 without fullness).** Row 11. `J` is not DF and `EL_n(J)` is not MF (`n >= 4`), yet `EL_n(J)` has a nontrivial MF quotient.
  So "no MF quotient" needs fullness or stable infiniteness (rows 8–10, 16), while "not MF" needs only a finite-order defect.
- **F5 (U4, the middle).** Row 16. Simple rings that are DF but not SF are on the paradox side. For simple rings the middle is among
  STABLY FINITE rings without LEF-ring models. Row 7 (Labbé) is the concrete candidate.
- **F6 (U3, characteristic `p`).** Tex Prop l.1072: `EL_4(R)` MF implies `R` DF, for every countable ring of positive characteristic.
