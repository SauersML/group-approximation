# EX review, wave 2, part 4: the remaining established claims (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tips `7d41d1a16` to `c0181d92f`.
Sources were fetched as arXiv PDFs on MSI, downloaded, and read locally, page by page, or with `pdftotext`.

## 0. Census corrections

- **Dropped as duplicates.** `ex-review-presentations-2026-09-12.md` §0 already PASSes `P -> L^x` and `Q -> L^x`
  with simplicity and nonsoficity. My strict matcher missed its prose form. So these four are removed from this
  census: `explicit-eighteen-relator-nonsofic-group`, `explicit-sixty-relator-nonsofic-group`,
  `leavitt-unit-group-steinberg-weyl-presentation` and `thompson-steinberg-presentation-of-leavitt-unit-group`.
- **Stale marker, outside the census.** `lef-of-finite-presentations-is-pi2-complete` still says "(unreviewed)",
  although `ex-review-groups-2026-09-12-part3.md` PASSes it. The complexity ledger's "(reviewed)" is correct.

## 1. Literature imports, checked against the source

| claim | source read | result |
|---|---|---|
| `almost-commuting-permutations-are-near-commuting` | arXiv:1410.2626: Main Theorem p. 2, Definition 3.2 p. 5, Open problem p. 3 | verbatim; PASS |
| `thompson-f-character-simplex` | arXiv:1212.1230: Definition 3.1 and the remark on p. 10; Corollary 3.3 p. 11 | verbatim; the Choquet step is standard; PASS |
| `nikolov-segal-uniform-commutator-width` | arXiv:math/0604399v1: Theorem 1.2 p. 2, "simple commutator" p. 3 | verbatim; PASS |
| `lucchini-menegazzo-unique-minimal-normal-generation` | Numdam scan, journal p. 174: Theorem 1.1 | verbatim; PASS |
| `hyperlinear-groups-closed-under-free-products` | arXiv:math/0609080v5: Corollary 4.5 (PDF p. 20); arXiv:0804.3968: Theorem 8.5 | verbatim. `L(H_1 * H_2) = L(H_1) * L(H_2)` with `B = C`. PASS |
| `leavitt-algebras-l-k-1-n-are-simple` | arXiv:1410.1835v1: Theorem 1.20 p. 10 | verbatim. The rose has trivial hereditary saturated sets, and each cycle (no repeated vertices, so one loop) has an exit when `n >= 2`. PASS |
| `thompson-v-cyclic-subgroups-are-undistorted` | arXiv:1107.0672v3: Theorem 1.3 | verbatim; PASS |
| `thompson-v-powers-have-linearly-growing-slope` | arXiv:1107.0672v3, proof of Theorem 1.3: slope formula `((2n-1)^(L_r))^(w+1) (2n-1)^(S(r,z))` | verbatim. A statement read from inside a proof. The repeller and `L_r >= 1` come from the paper's revealing-pair set-up. PASS as a reading |
| `bleak-quick-finite-presentations-of-thompson-v` | arXiv:1511.02123v2: Theorems 1.2 and 1.3 present as quoted | The words were not re-compared letter by letter; the owner compared them in TeX, plus an exact check in `L^x`. PASS |
| `leavitt-unit-group-finitely-presented` | arXiv:2609.08428v1: Theorem 6.1 "The group G = R× is finitely presented", with proof through Krstić--McCool and Theorem 5.4 | verbatim; PASS |
| `li-derived-full-group-homology-is-k-theory-cover` | arXiv:2209.08087 (current PDF) | content PASS, **citation note**, below |
| `ollivier-wise-kazhdan-rips-construction` | arXiv:math/0409203v1: Theorem 1.1 (1)--(4) | verbatim. **Strengthened**, below. PASS |

**Li, printed numbers.** The route quotes TeX labels and line numbers. The printed arXiv numbers are:
- item 1 is Theorem A = Theorem 4.18;
- item 2 is **Corollary 5.20**, verbatim "`H_*(D(G), C) ≅ H_*(D(R × G), C) ≅ H_*(Ω̃^∞_0 K(B_G), C)`" under "without
  isolated points, minimal, comparison", resting on Theorem 5.19;
- item 3 is the proof of **Theorem 6.12**.

These should replace the labels in the `-citation` route. Sent to the owner lane.

**Ollivier--Wise, asphericity.** The route rests "`cd G <= 2`" on the paper's summary sentence. This is independently
confirmed by D. Gruber, arXiv:1210.0178:
- Theorem 2.18: the presentation complex of a graphical `C(6)` presentation is aspherical.
- Corollary 2.19: "`G(Γ)` has an at most 2-dimensional `K(G(Γ),1)` space and hence cohomological dimension at most 2".
- `Gr'(1/6)` implies graphical `C(7)`.

The consumer `cd-two-group-with-infranormal-kazhdan-pair` is therefore on firm ground. Sent to the owner lane.

## 2. The two Thompson `F` equivalences: PASS

**`thompson-f-sofic-iff-relator-system-unstable`.**
- *Finite quotients are abelian.* `F'` is infinite and simple, so it dies in every finite quotient. Exact solutions
  in `Sym(n)` are the commuting pairs.
- *The character.* `χ(g) = lim |Fix φ_n(g)|/k_n` is positive definite, since
  `Σ c_i c̄_j |Fix(σ_j^(-1)σ_i)| = Σ_(x,y) |Σ_i c_i [σ_i x = y]|^2`. By Dudko--Medynets it is
  `t τ_reg + (1-t) χ_ab`, with value `1 - t` on `F' \ {e}`.
- *1 => 4.* If `t > 0`, `φ^(×m) × τ_N∘ab` has defect at most `m` times larger. Elements outside `F'` translate the
  torus freely once `N` is large, and elements of `F' \ {e}` fix a fraction `(1-t)^m`. So `F` is sofic.
- *4 => 3.* Evaluating fixed normal-form words on `δ_n`-solutions gives an almost-homomorphism. Its defects are
  bounded by van Kampen areas times `δ_n`, and `d(AB, BA) = d([A,B], id) >= ε` gives `t >= ε`.
- *3 => 2.* Arzhantseva--Păunescu for `k = 2`, with the quantifiers composed.
- *2 => 1.* Separation against stability.

**`thompson-f-hyperlinear-iff-relator-system-hs-unstable`.** The same scheme with traces.
- `||UW - WU||_2^2 = 2 - 2 Re tr[U,W]` gives `Re χ([a,b]) <= 1 - ε^2/2`.
- Tensor powers are Lipschitz in `||.||_2`.
- HS-stability of `Z^2` is imported from `chordal-abelian-graph-products-hs-stable`, not re-read here.

## 3. The left-orderable-nonsofic lane: PASS

**`relatively-kazhdan-amenable-pairs-allow-sofic-defects`.**
- `pI` is central, and `det(pI) = p^2 != 1`, so `Λ ≅ F_0 × Z`, which is locally indicable.
- Relative (T) is Navas p. 3, verbatim ("`F_2 ⋉ Z^2` still has the relative property (T)"). It passes to overgroups.
- Infranormality:
  - translations centralize `Z^2`;
  - `F_0` preserves `Z^2`, and `pI` compresses it;
  - `(pI)^(-1)Z^2(pI) = p^(-1)Z^2`.
- `G` is finitely generated (`p^(-k)e_i = (pI)^(-k) e_i (pI)^k`) and affine-linear, hence residually finite.
  Stabilizers are amenable. GKEP arXiv:2408.15470 Theorem 1.7 and arXiv:2401.04945 Theorem A (both verbatim) give
  that `H` is sofic.
- The defect is `t^(-1)γt = τ_(p^(-1)v_1) notin Z^2`.

**`rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group`.**
- *Displacement.* `d(g'e, e) <= 1/2 + (4δ+1) + 1/2`.
  - Any δ-convention mismatch with Delzant is harmless: the argument works with any displacement constant, by
    choosing `G_k` to miss a larger ball.
  - Delzant's note itself was not re-read.
- *The semigroup lemma.*
  - `psp^(e-1) in P ∩ N`, and `p^(±1)` normalizes `H'`.
  - Every element is congruent mod `H'` to a positive word, and `n ≡ w in P ∩ N`.
- *Infranormality.* `gΓ_kg^(-1) <= Γ ∩ G_k`.
- *Non-normality.* `[Γ : u^jΓu^(-j)] = f^j >= 2^j > [Γ : Γ_k]`.
- *Nonsoficity.* Kun--Thom 4.1 applied to `σ|E_k`. It needs `Γ_k`, `E_k` Kazhdan with `Γ_k` infranormal, which is
  step 2.
- *Unique products for extensions.* Checked through the fibre over the uniquely expressed `c̄`.

**`non-rf-hyperbolic-group-or-unique-product-nonsofic-group`.**
- PASS as a dichotomy: the case split is exhaustive, `W` is finitely generated by one lamp over a transitive `E_k`,
  and a domain is directly finite.
- **Justification note.** "The same argument shows that units are trivial" elides a step. A unique product group
  has the two unique products property (Strojnowski, 1980), and two unique products give trivial units. The
  conclusion is standard and correct.
- Imports not re-derived: `hyperbolic-kazhdan-cover-of-leavitt-unit-group` and
  `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`. I found no PASS for either in the review artifacts
  on main, so this dichotomy inherits their review state.

## 4. Presentations derived from the reviewed eighteen-relator proof: PASS

**`thompson-steinberg-three-generator-presentation`.** PASS at the checked steps. The three substitutions into the
PASSed Steps 0--5:
- Bleak--Quick Theorem 1.3 in place of Theorem 2.1.
- `ι_1(u)`, `ι_1(v)` generate the cone-1 copy of `V`, since `u, v` generate `V`. Their words are certified in `L^x`.
- Modulo `<<x>>`, `(u^3x)^3` gives `u^9 = 1`, and with `u^6 = 1` this gives `u^3 = (00 01) = 1`. So `V`, being
  simple, dies.

**`leavitt-units-two-generator-fifteen-relator-presentation`.** The Tietze argument re-derives:
- `[v, T] = 1`, `v^3 = T^2 = 1`, so `w^6 = 1`, `w^(-2) = v` and `w^3 = T`. All of these are consequences of the
  complete `R16`.
- After eliminating `v` and `x`, the added relators become free-group identities or the substituted `v^3`.
- The substituted `x^2` is `G^(-1)w^6G`, which is redundant.

## 5. `arithmetical-complexity-table-of-group-properties`: PASS at the ledger level

- **Statuses match the cells.** All 29 legend nodes exist on main. The cells marked OPEN point at open nodes:
  `sofic-safe-finite-presentation-compiler`, `amenability-of-finite-presentations-is-pi2-complete` and
  `metabelianity-of-finite-presentations-is-recursively-enumerable`. The other legend nodes carry ESTABLISHED
  markers with routes.
- **Folklore cells re-derived.**
  - Triviality: `Σ^0_1` on finite presentations, by Rabin; `Π^0_2` on enumerated presentations.
  - `contains F_2`: `∃(u,v) ∀w  w(u,v) != 1`, where `!= 1` is `Π^0_1`.
  - Metabelian: `Π^0_2`, and `Σ^0_1`-hard through the Rabin group.
- **The residually-`p` cell "as RF".**
  - `Π^0_2`: for every `w`, `w = 1` or some `p`-quotient separates `w`.
  - Not `Π^0_1`: `G_w` is trivial iff `w = 1`. Otherwise `G_w` contains a finitely presented group with unsolvable
    word problem, so it is not RF (McKinsey--Mal'cev), hence not residually `p`.
- **Not checked.** The Lean declaration names; the Bilanović--Chubb--Roven attribution (arXiv:1903.05143, not
  re-read); the market and press notes in "Prior and adjacent work".

## 6. Verdicts

All 23 remaining census items PASS, some with a note. None is a FAIL or a GAP.
- Citation notes (numbers to add): `li-derived-full-group-homology-is-k-theory-cover`; Gruber for
  `ollivier-wise-kazhdan-rips-construction`.
- Justification note: `non-rf-hyperbolic-group-or-unique-product-nonsofic-group` (Strojnowski).
- Reading note: `thompson-v-powers-have-linearly-growing-slope` is read from a proof, not a numbered statement.
