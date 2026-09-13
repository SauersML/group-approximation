# EX review 2, dynamics: part 1. ex-hs-instability-kazhdan, second pass

Lane `ex-verify2-dynamics`, tip `6dd68ce8d`. Commits under review: 3d19cd88eb, a52bf65b6f, a36fec7696,
e93af47046, 781c47abf0, 3689daa16b, bcd399dfb5, b08827ebd2. The first pass is `ex-review-backlog-2026-09-13`,
parts 5–7 (§§11, 20, 30, 33). The derivations below were redone independently.

| claim | verdict |
|---|---|
| `rf-kazhdan-group-not-flexibly-hs-stable` (+ `-proof`) | PASS |
| `bdhv-central-extension-property-t` (+ `-citation`) | PASS, verbatim against the source text |
| `finite-multiplier-projective-models-round-strictly` (+ `-proof`) | PASS |
| `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` (+ `-proof`) | PASS, including the corollary (§5 of the route) |
| `flexible-hs-stability-descends-to-retracts-finite-index` (+ `-proof`) | PASS, including the final comparison (§5 of the route) |
| `sl3-polynomial-congruence-subgroups-have-large-b2` (+ `-proof`) | PASS as a conditional on (S), with the `D = 2` rows re-derived by hand. The title was a wording FAIL, now corrected |
| routes `el-r-vertex-instability-via-rank-three-covers` and `el-r-vertex-instability-via-congruence-central-extension` | PASS as implications. Their premises are open, so neither route fires |
| credit quotes (Dogon arXiv:2211.10492v3, Ioana–Spaas–Wiersma arXiv:2006.01874v2) | PASS (§1.8) |

## 1.1 `rf-kazhdan-group-not-flexibly-hs-stable`: PASS

**(T) for `Γ_g = Z^(2g) ⋊ Sp_(2g)(Z)`, `g >= 2`.**
- Relative (T) of `(Π_i ⋊ SL_2(Z)_i, Π_i)` gives, on `H^(Π_i)^⊥`, the bound `κ_i||ζ|| <= max_(S_i)||π(s)ζ − ζ||`.
- `ζ = ξ − P_iξ` lies there, and `||π(s)ζ − ζ|| = ||(1 − P_i)(π(s)ξ − ξ)|| <= ||π(s)ξ − ξ||`.
- The `P_i` commute, and `P_N = P_1···P_g` projects onto `H^(Z^(2g))`. Writing
  `ξ − P_1P_2ξ = (ξ − P_1ξ) + P_1(ξ − P_2ξ)` and iterating gives `||ξ − P_Nξ|| <= Σ||ξ − P_iξ|| <= gδ/κ_1`.
- With `δ < min(κ_1/(2g), κ_0/2)`, `η/||η||` moves by less than `2δ < κ_0` over `S_0`. A nonzero
  `Sp_(2g)(Z)`-invariant vector in `H^(Z^(2g))` is `Γ_g`-invariant.
- Dependencies:
  - `elementary-linear-semidir-pair-relative-t` covers `R = Z`. Its import is Ershov–Jaikin-Zapirain–Kassabov,
    for finitely generated rings.
  - (T) of `Sp_(2g)(Z)` comes from item 3 of `deligne-universal-cover-lattice-is-non-rf-kazhdan`
    (`n = g >= 2`), passed to the quotient.

**The Heisenberg cover.**
- *Associativity.* Both sides equal `(v + Aw + ABu, s + t + r + ·, ABC)`. The middle entries agree iff
  `ω(Aw, ABu) = ω(w, Bu)`, which holds because `A` is symplectic.
- *Commutator.* `x_vx_w = (v+w, ω(v,w), 1)`, `(x_wx_v)^(−1) = (−v−w, −ω(w,v), 1)`, so `[x_v,x_w] = z^(2ω(v,w))`.
- *Finite abelianization.*
  - `y_Ax_wy_A^(−1) = x_(Aw)`.
  - The transvection `T_u` has `(T_u − 1)x = ω(u,x)u`, so the coinvariants of `Z^(2g)` vanish and
    `[x_w] ∈ ⟨[z]⟩`, of order `<= 2`.
  - Together with finiteness of `Sp_(2g)(Z)^ab`, this makes `Γ~_g^ab` finite.
- *Non-split.* A splitting would make `Γ~_g ≅ Z × Γ_g`, with infinite abelianization. So Dogon's Theorem 1.3
  applies as the node says.

**Models and non-rounding.**
- *Defect.* `s(g)s(h) = (v + Aw, ω(v,Aw), AB) = z^(ω(v,Aw))s(gh)`.
- *Trace.* The normalized trace of `λ(x)E` is `Σ_j e^(−2πij/k)τ(xz̄^j) = e^(2πim/k)` if `x = z̄^m`, and `0`
  otherwise.
- *Bimodule representation.* In `σ_k`:
  - `α(g)P − Pπ(g) = (α(g) − Pπ(g)P*)P − Pπ(g)(1 − P*P)`.
  - The first term has columns in `range P*P` and the second in its complement, so they are HS-orthogonal.
  - `||XP||_(2,d) = ||X||_(2,d)`, since `PP* = 1`, and the second term has square norm `<= (D − d)/d`.
- *Quantitative form.*
  - Each `s(F)`-letter moves `P` by at most `(ε^2 + ε)^(1/2) <= ε + √ε <= 2κ/(3L)` when
    `ε = min(1, (κ/(3L))^2)`.
  - The letter `z` moves it by `|e^(2πi/k) − 1| <= 2π/k < κ/(3L)` when `k > 6πL/κ`.
  - A word of length `<= L` therefore moves `P` by less than `κ`.

## 1.2 `bdhv-central-extension-property-t`: PASS

The first pass read the quotation, not the source. Here the source was read.
- `/scratch.global/sauer354/bh-rn/bdlhv.txt`, line 2860: "Theorem 1.7.11 Let G be a locally compact group and C
  a closed subgroup contained in the centre of G. Assume that G/C has Property (T) and that G/[G,G] is compact.
  Then G has Property (T)."
- Line 2871: Remark 1.7.12 (i), as quoted.
- The discrete specialization is immediate.

## 1.3 `finite-multiplier-projective-models-round-strictly`: PASS

- `Ext(H_1, T) = 0` because `T` is divisible. So `H^2(Γ;T) ≅ Hom(H_2(Γ;Z), T)`.
- If `e[z_j] = 0`, then `ez_j = ∂w` and `c_n(z_j)^e = (δc_n)(w) = 1`. So `c_n(z_j) ∈ μ_e`, a discrete set, and
  `c_n(z_j) → 1` forces `c_n(z_j) = 1` eventually.
- The gauge `π' = b^(−1)α` is a homomorphism.
- *The ultrafilter step.* `b_ω` is a character. `X = Hom(Γ,T)` is finite, so the minimizers `χ_n` give
  `β_n = b_nχ_n^(−1)` with `δβ_n = c_n` and `β_n(s) → 1`.
- *Induction.* `β(gs) = β(g)β(s)c(g,s)^(−1)`, `β(s^(−1)) = c(s,s^(−1))β(e)β(s)^(−1)` and `β(e) = c(e,e)`. So
  `β_n → 1` pointwise.
- The Kun–Thom instance is labelled "not source-verified" and is not claimed.

## 1.4 `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`: PASS

- **(c) ⇒ (b).** `ρ_k(s(g))` preserves `Fix_N` and its complement, and acts on `Fix_N` as `π'_k(g)`. So
  `||α_k(g) − π'_k(g) ⊕ 1||_2 = ||(ρ_k(s(g)) − 1)(1 − E_k)||_2 <= 2(1 − tr E_k)^(1/2)`.
- **(a) ⇒ (c).**
  - On `M_0 ⊆ N`, `σ_k(m)P − P = (ρ_k(m) − 1)P`, of norm `||ρ_k(m) − 1||_(2,d)`.
  - An invariant `η` satisfies `ρ_k(m)η = η` for `m ∈ N`, so `E_kη = η`.
  - `1 − tr E_k = Tr(P*(1 − E_k)P)/d = ||(1 − E_k)(P − η)||^2 <= δ_k^2/κ^2`.
- **The corollary (§5, now read line by line).**
  - Irreducible summands `ρ'_j` nontrivial on `K_(L_j)` exist.
  - (KC1) holds exactly: `ρ_j(n_l) = 1` once `L_j >= l`.
  - `Fix_N(ρ_j)` is `Γ~`-invariant, hence `0` by irreducibility. So `tr E_j = 0`, and no subsequence rounds.
    Bounded dimensions are allowed: the argument never uses `d_j → ∞`.
- **Profinite version.**
  - If every finite-dimensional representation of `Γ_L` is trivial on `K_L`, then `K_L` lies in every
    finite-index normal subgroup. So `Γ^_L → Γ^` is injective, hence an isomorphism, and `Γ^` is finitely
    presented as a profinite group.
  - The argument uses one `L` at a time, so the contrapositive gives the hypothesis for every `L`, and in
    particular for all large `L`. The route supposes "for all `L >= L_1`" but uses only `L_1`. This is
    harmless.
- **Shalom's theorem.** Every Kazhdan group is a quotient of a finitely presented Kazhdan group. This is
  `fpbs-shalom-property-t-is-open`, established, not re-read here.

## 1.5 `flexible-hs-stability-descends-to-retracts-finite-index`: PASS

- **Retracts.** `α∘r` is asymptotic, and `π_n∘i` rounds `α`, because `r∘i = id`.
- **Induction.**
  - From `gg't_i = t_(σ_gσ_(g')(i)) h(g, σ_(g')(i)) h(g', i)` we get `σ_(gg') = σ_gσ_(g')` and a cocycle
    identity for `h`.
  - The block defects of `A_n` average those of `α_n`.
  - For `h ∈ H`, `A_n(h)` is a block permutation fixing block 1, so it commutes with `Q_1`.
- **Commutator bound.** Write `π(h) = P*(Pπ(h)P*)P + R` with `||R||_(2,D) <= 2((D − md)/D)^(1/2)`. Then
  `[P*XP, P*Q_1P] = P*[X − A(h), Q_1]P`, which gives the stated `2||A − Pπ P*|| + 4((D − md)/D)^(1/2)`.
- **Kazhdan projection.** `T_n` is self-adjoint, because the commutant is `*`-closed and `*` is an isometry
  preserving it. `E_n = 1_((1/2,∞))(T_n)` minimizes `||T_n − R||_2` over all projections `R`, so
  `||E_n − Q||_2 <= 2||T_n − Q||_2`.
- **Rank.** `|tr E − tr Q| <= ||E − Q||_2^2` holds for projections.
  - `E − Q` has spectrum in `[−1,1]`.
  - By the two-projection theory its eigenvalues in `(−1,1) ∖ {0}` come in pairs `±λ`.
  - So `tr(E − Q) = mult(1) − mult(−1)`, while `tr((E − Q)^2) >= mult(1) + mult(−1)`.
- **Comparison (§5, not read in the first pass).** Let `V` be the polar part of `EQ` and `s` its support
  projection, with `s <= Q`.
  - `||EQ − Q||_2 <= ||E − Q||_2`.
  - `||Q − (QEQ)^(1/2)||_2 <= ||Q − QEQ||_2`, because `1 − √x <= 1 − x` on `[0,1]`.
  - `tr(Q − s) = ||(E − Q)(Q − s)||_2^2 <= ||E − Q||_2^2`.
  - Hence `||V − Q||_2 <= 3||E − Q||_2`.
  - `π(h)` commutes with `E`, so `V*ρ(h)V = V*π(h)V`. This is within `6||E − Q||_2` of `Qπ(h)Q`, and `Qπ(h)Q`
    is within `m^(1/2)||A(h) − Pπ(h)P*||_(2,md)` of `α(h)` in the `d`-normalization.
  - Pad `ρ` with `C^(tr(Q − s)·D)` carrying the trivial representation, and send `range(Q − s)` isometrically
    onto it. The resulting isometry `W` has `D' >= d` and `D'/d → 1`, since `rank E − d = o(d)`.

## 1.6 `sl3-polynomial-congruence-subgroups-have-large-b2`: PASS as a conditional; title corrected

**Statement.** Hypothesis (S), Soulé's strict fundamental domain, is named in the body, and the theorem is
stated under it. So `requires: []` establishes the conditional statement.
- Soulé (*Chevalley groups over polynomial rings*, LMS Lecture Notes 36, 1979) is not imported as a node, and
  I did not read it.
- **Wording FAIL.** The title said "Congruence subgroups ... of level degree at least 2 have large second Betti
  number". The body proves this at ten computed levels only, under (S). Corrected forward: the title now names
  (S) and the computed levels.

**Stabilizers and images.**
- `g_ij t^(a_j − a_i) ∈ F_q[[1/t]]` iff `deg g_ij <= a_i − a_j`.
- For `i > j`, `d_ij >= 0` iff `a_i = a_j` on the whole cell, and then `d_ij = d_ji = 0`. So the stabilizer is
  block upper triangular, with Levi blocks over `F_q`.
- The image order is `|S(Π GL_(n_k)(F_q))|·Π q^(min(d_ij+1, D))`.
- The set is closed under products because `d_ik + d_kj <= d_ij`.
- Double cosets: `Γ(f)\Γ/Γ_σ ≅ SL_3(A)/π(Γ_σ)`.
- Rational comparison: the stabilizers are finite and the action is type-preserving.
- Integral classes:
  - `H_2(Y;Z)` is a subgroup of a free abelian group, and `Y` retracts onto the finite `Y_(R_0)`.
  - So `H^2(Y;Z) ⊗ R → H^2(Y;R)` is onto.
  - For the Z-extension to have finite abelianization, use the five-term sequence
    `H_2(Γ(f)) → Z → H_1(Γ~) → H_1(Γ(f)) → 0`. It shows that a class with nonzero real image gives a finite
    `H_1(Γ~)`.

**Collapses (§3 of the route, checked cell by cell).**
- *Triples.* `τ_b: (R−b, R, b)` and `ε_b: (R−b, R+1, b)`. `σ_b: (R−b−1, R, b)`, `e_b: (R−b, R, b)` and
  `f_(b+1): (R−b−1, R, b+1)`. `w_b: (R+1−b, R+1, b)`, `f_b: (R−b, R, b)` and `e_(b−1): (R+1−b, R, b−1)`.
- *Flags.* `L_23` holds for `f_0, w_0`, and `L_12` for `e_R, w_(R+1)`. No other cell has a flag.
- *Equalities.* `m(R) = m(R+1)` needs `R >= D − 1`. Through `e_b`, `m(R−b) = m(R−b−1)` needs `b <= R − D`.
  Through `f_(b+1)`, `m(b) = m(b+1)` needs `b >= R − D + 1 >= D − 1`.
- *Freeness.* After step 1, `e_b` and `f_(b+1)` lie only in `σ_b`. After step 2, each `w_b` lies on exactly one
  surviving new edge: `f_b` for `b <= R − D + 1`, and `e_(b−1)` otherwise.
- *Strict fundamental domain.* Cofaces of lifts are lifts of cofaces, so each lift of a free face lies in exactly
  one lift of its coface when the images agree.

**Hand re-derivation of the `D = 2` rows.** Put `c(q,D) = Σ_(σ ⊂ Q_2) (−1)^(dim σ)/|π(Γ_σ)|`. `Q_2` has 6
vertices, 9 edges and 4 triangles.
- **`q = 2`.** The image orders are:
  - vertices: 168, 96, 96, 96, 64, 96;
  - edges: 24, 24, 16, 96, 32, 32, 96, 32, 32;
  - triangles: 8, 32, 32, 16.

  Over the denominator 1344: `c = (85 − 392 + 336)/1344 = 29/1344`. With `|SL_3(F_2[t]/t^2)| = 43008`,
  `|SL_3(F_2)|^2 = 28224` and `|SL_3(F_4)| = 60480`, this gives χ = 928, 609 and 1305, matching the table.
- **`q = 3`.** The image orders are:
  - vertices: 5616, 3888 (×4), 2916;
  - edges: 432 (×2), 324, 3888 (×2), 972 (×4);
  - triangles: 108, 972 (×2), 324.

  Over the denominator 151632: `c = (235 − 1872 + 2184)/151632 = 547/151632`. With `|SL_3(F_3[t]/t^2)| = 36846576`,
  `|SL_3(F_3)|^2 = 31539456` and `|SL_3(F_9)| = 42456960`, this gives χ = 243·547 = 132921, 208·547 = 113776 and
  280·547 = 153160, matching the table.
- **Also checked.** The `R = 1` hand check (256), and `b_1 = 0` from (T).
- **Not re-derived.** The `D = 3` rows. The script was read line by line: `sl3_A_order`, `image_order`
  (blocks, Levi order `Π|GL_n|/(q−1)`, upper entries), `cells` and `chi`. It implements exactly the formula above.

## 1.7 Conditional routes into `el-r-polynomial-vertex-not-flexibly-hs-stable`: PASS as implications

- **Rank-three covers.** This is the corollary of §1.4 at `SL_3(F_q[t])`, followed by the retract `x_1 ↦ t`,
  `x_j ↦ 0`. `EL_3(F_q[t]) = SL_3(F_q[t])` because `F_q[t]` is Euclidean.
- **Congruence central extension.**
  - `Δ` has finite index in the Kazhdan lattice `SL_3(F_q[t]) <= SL_3(F_q((1/t)))`, so it is Kazhdan, and
    `Δ~` is Kazhdan by §1.2.
  - The central characters `e^(2πi/n_k)` give (KC1) with `Fix = 0`.
  - Then descend through items 2 and 1 of §1.5.
- **Firing.** Both premises (`sl3-polynomial-covers-have-extra-finite-quotients` and
  `sl3-polynomial-finite-index-z-extension-center-survives`) are OPEN at `6dd68ce8d`, so neither route fires.
- **The Attempts claim** "integral classes with nonzero real image give central Z-extensions with finite
  abelianization" follows from the five-term sequence in §1.6.

## 1.8 Credit quotes against the sources

- **Dogon, arXiv:2211.10492v3** (text extraction `/scratch.global/sauer354/bh-rn/2211.10492.txt`).
  - *Definition 1.2 (p. 2).* Flexible HS-stability: asymptotic homomorphisms `φ_n : Γ → U(d_n)`, genuine
    `π_n : Γ → U(D_n)` with `D_n >= d_n`, `lim D_n/d_n = 1`, and `||φ_n(g) − P_nπ_n(g)P_n||_(2,τ_(d_n)) → 0`.
    This matches the nodes.
  - *p. 3.* "Ioana, Spaas and Wiersma [28] showed that SL_2(Z) ⋉ Z^2 is not flexibly HS-stable, giving the first
    residually finite example. For groups of very different nature, Ioana [31] proved that F_m × F_k is not
    flexibly HS-stable". This matches the novelty note.
  - *Theorem 1.3.* `Γ` is a countable property (T) group and `A` a countable torsion-free abelian group, with a
    non-split central extension `1 → A → G → Γ → 1`. Assume either that `Γ` is perfect, or that `G` has (T)
    and `A = Z`. "If Γ is flexibly HS-stable, then G is not hyperlinear."
  - *Theorem 1.10.* "Let Γ be an infinitely presented property (T) group. If Γ is weakly ucp-stable, then there
    exists a non-hyperlinear group." The text then continues: "an explicit example of an infinitely presented
    property (T) group is SL_3(F_p[X])".
- **Ioana–Spaas–Wiersma, arXiv:2006.01874v2, p. 2, Theorem A.** `(Γ,Λ)` has relative (T), and the cocycles
  `c_n ∈ Z^2(Γ,T)` satisfy three conditions: `c_n|Λ` is not a coboundary, `c_n → 1`, and there are
  finite-dimensional projective representations with cocycle `c_n`. "Then C*(Γ) does not have the LLP."
  - §6 of the rf-kazhdan route checks these hypotheses.
  - For abelian `Λ`, a coboundary is symmetric, and `c_k(e_1,f_1) != c_k(f_1,e_1)`.
- **The ISW remark** (arXiv:2006.01874v2, introduction, `pdftotext` lines 286–289): "In particular, any group Γ
  satisfying the hypothesis of Theorem A (e.g., Γ = Z2 ⋊ SL2(Z)) is not flexibly HS-stable in the sense suggested
  in [BL20, Section 4.4]." This matches the node's quotation.
- **Novelty.** The check stays bounded, as the node says. Neither source names a Kazhdan instance: ISW's examples
  on pp. 2–5 are LLP and LP failures, and Dogon's p. 3 list is quoted above.
