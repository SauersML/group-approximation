# EX review, wave 2, part 2: classical relator width (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tip `7d41d1a16`.
Sources: `research/artifacts/classical-relator-width-part1-class-sizes-2026-09-13.md` (after the 513d2f1740 fix)
and `...-part2-commutator-choice-2026-09-13.md`. The backlog pass (`ex-review-backlog-2026-09-13-part7.md` §27.1)
checked these at the step level. Here the lemmas the brief names are re-derived from scratch.

## 1. Part 1 Lemma 1.4 (consumed by Lemma 4.2): PASS

- *Item 1, (O).* `Q(xe + yf_0 + w) = xy + Q(w)`, and `xy = c` has at least `q - 1` solutions. So there are at least
  `(q-1)q^(k-2) >= q^(k-1)/2` singular vectors.
- *Item 1, (U).* `β(v,v) = Tr(x̄y) + β(w,w)`. For `x != 0`, `Tr(x̄y) = c` is an affine `F_q`-hyperplane of `F`, which
  gives at least `(q^2-1)q` pairs. Then `(q^2-1)q^(2k-3) >= q^(2k-2)/2`.
- *Item 2.* `β(e, v) = y`. In (O), `x = -Q(w)` is forced. In (U), `Tr(x) = -β(w,w)` has `q` solutions.
- The count of item 1 may include `0`. Lemma 4.2 counts `0` among the failures (`0 in S_(j-1)`), so nothing breaks.

## 2. Part 1 Lemma 2.1 (big cell): PASS

- **Levi and radical.**
  - `m(x)` is an isometry. In (O), `Q(xa + x^(-†)b + c) = β(a,b) + Q(c)`, because `L` and `L'` are totally singular.
  - For `u_S`, the expansion gives `β(u_S v, u_S v') = β(v,v') + β(Sb,b') + β(b,Sb')`, and in (O) also
    `Q(u_S v) = Q(v) + β(Sb, b)`. So the admissible `S` are symmetric (Sp, `m(m+1)/2`), alternating (O,
    `m(m-1)/2`), or skew-hermitian (U). In (U) the diagonal entries have trace `0`, which gives an
    `F_q`-dimension of `m + m(m-1) = m^2`.
- **`U <= I(V)'`.**
  - `u_S u_(S') = u_(S+S')`, and `m(x) u_S m(x)^(-1) = u_(xSx^†)`, which I checked by applying both sides to
    `a + b + c`. So `[m(x), u_S] = u_(xSx^† - S)`.
  - Off-diagonal basis forms come from elementary substitutions, using `m >= 3`.
  - Diagonal entries come out as `λ^2` multiples (Sp) or `N(λ) ε` multiples (U). Squares additively generate `F_q`,
    and the norm maps onto `F_q^×`. So the commutators generate all of `U`.
- **Big cell.** `U^- ∩ P = 1`, since `a + S'a in L` for all `a` forces `S' = 0`. And `m(SL(L)) ∩ U = 1`, since Levi
  elements fix `L'` and `u_S` fixes `L'` only when `S = 0`. So `U^- × m(SL(L)) × U -> Q_0` is injective.
- **Order.** `|SL_m(q_F)| = q_F^(m^2-1) Π_(i=2)^m (1 - q_F^(-i)) >= 0.57 q_F^(m^2-1) >= q_F^(m^2-1)/4`.
- **Exponents.**
  - `2m^2 + m - 1`, `2m^2 - m - 1` and `4m^2 - 2`.
  - With `n = 2m + e_0`: `n(n+1)/2 - E_0` is `1` (Sp) and `m(2e_0+2) + e_0(e_0+1)/2 + 1 <= 3n+4` (O, `e_0 <= 2`).
  - `n(n+1) - E_0 = 2m(2e_0+1) + e_0(e_0+1) + 2 <= 3n+4` (U, `e_0 <= 1`).

## 3. Part 1 Lemmas 3.1 and 3.2 (class sizes): PASS

- **Lemma 3.1.**
  - `T = E^⊥` has dimension `s`, and `T^⊥ = E`, so `span(g e_(<i)) ∩ T^⊥ <= T ∩ E` has dimension at most `r`.
  - The `i - 1` constraints are `F`-linear in `g e_i`: in (U), `β` is linear in the second variable. Their rank on
    `A` is at least `(i-1) - dim(span ∩ A^⊥)`.
  - The block bounds are `s - i + 1 + r` for `T`. For `E` and `V` the bound is `n - i + 1`, because the span
    contains `T` and `V^⊥ = 0`. When `i <= r + 1` the `T`-bound exceeds the trivial cap `s`, and it is still an
    upper bound.
  - The sum is `s(s+1)/2 + rs + (n-s)(n-s+1)/2`.
- **Lemma 3.2.**
  - Distinct fixed spaces give distinct conjugates, so `|k^(Q_0)| >= |Q_0|/|Stab_(I(V))(E)|`.
  - The identity `s(s+1)/2 + (n-s)(n-s+1)/2 = n(n+1)/2 - s(n-s)` gives exponents `s(n-s) - rs - 1 >= s(n-2s) - 1` (Sp).
    (O) is the same minus a further `3n + 3`.
  - (U) has `2s(n-2s) - 3n - 4 >= s(n-2s) - 3n - 4`.
  - `n >= 8` gives Witt index `m >= 3` in all three cases, so Lemma 2.1 applies.

## 4. Part 2 Lemmas 4.1 and 4.2 (commutator choice): PASS

- **Lemma 4.1.** `[h,y] - 1 = (hNh^(-1) - N)y^(-1)`. On `hK` the operator is `-N`, which gives the lower bound
  `dim hK - dim(hK ∩ K)`.
- **Choosing `e_j`.**
  - `R` has dimension `n - 2j + 2 >= 7n/8 + 2 >= 30`.
  - The failures lie in `S_(j-1)` or in `(h-λ)^(-1)S_(j-1)` for some `λ in F`. That is at most
    `q_F^(4j-4) + q_F · q_F^(n-ρ+4j-4) <= 2q_F^(n-ρ+4j-3)` vectors.
  - Lemma 1.4(1) gives at least `q_F^(n-2j+1)/2` singular vectors.
  - The ratio is at least `q_F^(ρ-6j+4)/4 >= q_F^4/4 >= 4`, because `ρ >= 6r' >= 6j`.
- **Choosing `f_j`.** At least `q_F^(n-2j)` partners exist, against `|B| <= q_F^(4j-2)`. The first is larger because
  `n > 6j - 2`, which follows from `j <= n/16`.
- **The element.**
  - `p(t) = t^(r') + at + (-1)^(r')` has `det C = 1`, and `p(1) = 1 + a + (-1)^(r') != 0`.
  - `C^(-†)` has eigenvalue `1` only if `C` does.
  - `y = m(C) in m(SL_(r')) = m(SL_(r'))' <= I(V)'`, since `r' >= 3`.
- **Rank.**
  - `h(Y^⊥) = (hY)^⊥`, so `K ∩ hK = (Y + hY)^⊥`. The lower bound is `dim(Y + hY) - 2r' >= r'`.
  - `dim(Y + hY) >= 3r'`, because each step adds `e_j`, `he_j`, `f_j` independently modulo `S_(j-1)`.

## 5. Part 2 Lemma 5.3 (displacement): PASS

- **Witt index.** `W^⊥` has dimension at least `6d_0 + 2d' + 2`, so its Witt index is at least `3d_0 + d'`
  (`dim V_0 <= 2`).
- **Copies of `W`.**
  - The diagonal of `W ⊕ W^-` is totally singular of dimension `d_0`.
  - The hyperbolic induction works: `Δ ∩ f^⊥` has dimension exactly `d_0 - 1`, because `β(e,f) = 1`, and it lies in
    `span(e,f)^⊥`.
  - Equal-dimensional hyperbolic spaces are isometric.
- **The conjugation `g s g^(-1) = s'`, checked on all four summands.**
  - On `W_3`: `w_3 -> σ_3^(-1)w_3 -> σσ_3^(-1)w_3 -> σ_4σ_3^(-1)w_3 = σ'w_3`.
  - On `W_4`: `w_4 -> σσ_4^(-1)w_4 -> σ_4^(-1)w_4 -> σ_3σ_4^(-1)w_4 = σ'^(-1)w_4`.
  - On `W` and `W_1`: the identity.
- **`y = ss'`.** `y in I(W''')'`, since `s` and `s'` are conjugate involutions and so agree in the abelianization.
- **The commutator.** `[h_0,y] = h_0 s h_0^(-1) s`, because `s'` commutes with `h_0` and with `s`. `s h_0^(-1) s` is
  `1` on `W` and `σh_0^(-1)σ^(-1)` on `W_1`.

## 6. `non-linear-sofic-simple-groups-bounded-width-in-classical-groups`: PASS (assembly)

Route `classical-width-from-finite-field-linear-sofic-dichotomy`:
- **Step 1.**
  - `GL_n(F_p) <= GL_n(F_q)` preserves rank.
  - Restriction of scalars multiplies rank and dimension by `e`, so it preserves normalized rank.
  - So "not linear sofic over `F_q`" means "not `F_p`-linear sofic".
- **Step 2** is item 2 of `simple-group-psl-width-is-finite-field-linear-soficity` verbatim: fixed characteristic,
  `Q = SL_n(p^e)/Z_0`.
- **Step 3** is the fixed-characteristic clause of `simple-group-classical-width-finite-field-linear-soficity`, for
  `Q_0 in {Sp_n, SU_n, Omega^±_n}(p^e)` with simple central quotient. `SU_n(q)` lives over `F_(q^2)`, which has the
  same characteristic.
- **Note.** The claim says `Omega_n(q)`, and the classical node says `Omega^±_n`. Part 1's case (O) covers all
  nondegenerate quadratic spaces, odd `n` included (with `n` even when `q` is even). So the families match, and
  only the notation differs.
- **The quasisimple hypothesis** excludes exactly the non-simple small cases the classical node excludes.

## 7. Verdicts

| claim | verdict |
|---|---|
| `simple-group-classical-width-finite-field-linear-soficity` | PASS on part 1 Lemmas 1.4, 2.1, 3.1, 3.2 and part 2 Lemmas 4.1, 4.2, 5.3, independently re-derived. With §27.1 (route and 5.1--5.2), fully reviewed |
| `non-linear-sofic-simple-groups-bounded-width-in-classical-groups` | PASS as an assembly of two reviewed theorems |

**Not re-read.** The two recalled facts that the owner lane flags: `PSp`, `PSU`, `PΩ` are simple, and `I(W)'` is
`Sp`/`SU`/`Ω` for `dim W >= 9`. Both are standard (Kleidman--Liebeck, Ch. 2), and no source was re-read here.
