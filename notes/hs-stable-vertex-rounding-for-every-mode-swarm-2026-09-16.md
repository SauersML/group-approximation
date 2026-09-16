# hs-stable-vertex-rounding-for-every-model: swarm lane notes (2026-09-16)

- **Target and hole worked:** `hs-stable-vertex-rounding-for-every-model`, hypothesis (H1) of
  `hs-rounding-and-actor-gap-force-ccr` over every infranormal, non-normal Kazhdan pair and every
  trace-preserving model.
- **Outcome:** the general form is refuted, unconditionally, at an explicit residually finite pair with an
  explicit model. The Theorem E instance, which is the only use the unit-type chain makes of the claim, is
  untouched. It is now its own open claim.
- **Details:** `research/artifacts/vertex-rounding-product-pair-2026-09-16.md`. No scripts: the lane is
  pure proof.

## Setup

(H1) at a pair `Γ < G`: for every trace-preserving `σ : G -> U(prod_U M_n)`, the restrictions `σ_n|Γ` are
`o(1)`-close on a Kazhdan set `F` to genuine representations, after `o(n)` padding.
- Before this lane, the node listed two scope bullets against the general form: the nine-leaf Leavitt pair
  and the Fournier--Facio pair. Both refute it only if a particular group is hyperlinear.
- The downstream uses were `theorem-e-vertex-unit-type-via-deep-root-mass` (Theorem E pair only) and
  `hs-normalization-via-vertex-rounding-and-actor-gap` (the general target `kt-centralizer-normalization-hs`).
- The Theorem E attempts on the node (literal commutant, robust spectral gap, uniform Kazhdan constants,
  congruence projections, zero-one after an actor-invariant split) are all specific to `K < H`.

The lane question was whether the general form can be refuted without a hyperlinearity input.

## What was proven

**Theorem (artifact §2--§6, Remark 6.3).** Let `g >= 2`, `Γ_g = Z^(2g) ⋊ Sp_(2g)(Z)`, and let `K < H` be the
Kun--Thom Theorem E pair. Then `Γ = Γ_g × K < G = Γ_g × H` is an infranormal, non-normal pair of residually
finite Kazhdan groups. For every nonprincipal `U` there is a trace-preserving `σ : G -> U(prod_U M_n)` at
which (H1) fails for every finite generating set of `Γ`, under normalized padding and under Dogon's
compression reading.

Proof outline.
1. **Readings (§0).** Both readings give genuine `π'_n` on `C^(D_n)`, `D_n/n -> 1`, close to `σ_n ⊕ 1` in
   `||·||_(2,D_n)`. The compression error is bounded by the `(1,1)` block error plus `6(D_n - n)/D_n`. The
   estimate propagates along words, so the generating set does not matter.
2. **(T) facts (§1), proved in full.** Kazhdan sets generate, Kazhdan groups have finite abelianization, and
   there is an explicit Kazhdan pair for a product.
3. **The pair (§2).** `P_Γ = Γ_g × P_K` generates `G`. Non-normality comes from `K < H`.
4. **Heisenberg cover (§3).** `Γ~_g`, with cocycle `ω(v, Aw)`, has finite abelianization: `2[z] = 0`,
   transvections kill `Z^(2g)` modulo `[z]`, and `Sp_(2g)(Z)^ab` is finite. By the BdHV central-extension
   theorem it is Kazhdan.
5. **Uniform amplified obstruction (§4, Lemma 4.1).** Let `ρ` be a genuine representation of `Γ~_g` with
   `ρ(z) = ζ ≠ 1` scalar, and suppose `π : Γ_g -> U(D)` compresses to within `ε` of `ρ∘s` with slack
   `(D - d)/d <= ε`. Then the vector `P` in the bimodule `ξ -> ρ(x) ξ π(q(x))*` moves by at most
   `L·max(ε + √ε, |ζ - 1|)` under `Q~`. That bimodule has no invariant vectors. The constants `L`, `κ~` do
   not depend on `d`, so amplification by `1_m` cannot help.
6. **The model (§5, Remark 6.3).** `α_(k_j) ⊗ λ_j`: projective Heisenberg models of
   `rf-kazhdan-group-not-flexibly-hs-stable` tensored with permutation representations on a residual chain of
   `H`. For a fixed `U`, amplify by `1_(t_n)` and pad by `r_n < N_(j(n)) <= n^(1/2)`.
7. **Failure (§6).** Given a rounding, restrict it to `Γ_g × e`, compress to the Heisenberg block, and apply
   Lemma 4.1 at a large coordinate.

**Mechanism, and what a correct general form must exclude.** A vertex with a Kazhdan direct factor `Λ`
whose trace-preserving asymptotic representations stay non-roundable after amplification can always be
multiplied onto an infranormal Kazhdan pair. A true general statement must restrict the vertex beyond (T),
residual finiteness and infranormality. Finite `H_1` and `H_2` is a natural candidate: it voids scalar
cocycle models by `finite-multiplier-projective-models-round-strictly`. Whether it suffices is not addressed.

## Graph changes

- **New claim** `vertex-rounding-fails-at-symplectic-product-pair` (ESTABLISHED, unreviewed), with route
  `vertex-rounding-fails-at-symplectic-product-pair-proof`. The route requires `kun-thom-nonsofic-wreath`,
  `rf-kazhdan-group-not-flexibly-hs-stable` (items 1 and 2) and `bdhv-central-extension-property-t`.
- **Target node:** `refuted_by: vertex-rounding-fails-at-symplectic-product-pair`, status line and a first
  Attempts bullet. The statement is kept verbatim.
- **New open claim** `theorem-e-vertex-rounds-at-every-actor-model`: (H1) at `K < H` only, with inherited
  attempts and a transfer attempt.
- **New route** `theorem-e-unit-type-via-instance-vertex-rounding` for
  `theorem-e-vertex-rounds-to-unit-type-representations`. It is the deep-root-mass route with the premise
  restated at the instance. The other four premises are unchanged.
- `kt-actor-model-with-totally-non-roundable-vertex`: `refuted_by` moved from the general claim to the
  instance claim. That claim is exactly the negation of the instance at parameters with `gcd(r, q-1) = 1`.
- `hs-normalization-via-vertex-rounding-and-actor-gap` and `hs-normalization-via-vertex-rounding-and-liftable-masa`
  become invalid and have no replacement. Their target, `kt-centralizer-normalization-hs`, is general, and no
  Theorem E instance of that target was created.
- `check.sh` exit 0 on the seven research paths.

## Approaches and where they die

1. **Rounding at the Theorem E pair directly.** All earlier attempts on the node die as recorded there.
   Nothing new was tried on the instance beyond the transfer check below.
2. **A counterexample with no hyperlinearity input (succeeded).** The product with `Γ_g` above.
   - A first worry was that the `Γ_g`-models of `rf-kazhdan-group-not-flexibly-hs-stable` are non-roundable
     only at their own dimension. Tensoring with `λ_j` amplifies them by `1_(m_j)`.
   - Lemma 4.1 settles this: the Kazhdan constants of `Γ~_g` are independent of the amplification, and the
     compression slack enters only through `√ε`.
3. **Transferring the mechanism to `K` itself (dies).**
   - The mechanism needs a non-torsion class in `H^2` of a Kazhdan factor, together with (T) of the cover.
   - `K` has finite `H_1`. In the stable range `r >= d + 3`, `H_2(K; Z) = K_2(F_q) = 0` (van der Kallen and
     Quillen imports, unverified, recorded on `kt-actor-model-with-totally-non-roundable-vertex`).
   - So scalar cocycle models of `K` round strictly. A witness at `K < H` needs non-scalar defects that extend
     to the actor, and no non-scalar amplification-robust obstruction for `EL_r` over polynomial rings is
     known.
4. **Weakening the refutation's dependence on the reading.** Both paddings and a fixed or chosen ultrafilter
   are covered (Lemma 0.1, Remark 6.3). A reading of (H1) with unnormalized dimension growth `n'/n -> c > 1`
   is not in use in the graph and was not examined.

## Weakest points

- **Scope.** The node's statement quantifies over every pair, and this lane refutes that. If the intended
  meaning was only the Theorem E pair, the substance moves to `theorem-e-vertex-rounds-at-every-actor-model`,
  which is still open.
- **Imports.** Item 1 of `rf-kazhdan-group-not-flexibly-hs-stable` ((T) and residual finiteness of `Γ_g`) and
  item 2 (the models `α_k` and their traces) are established but unreviewed. Theorem E is a 2026 preprint
  result, source-verified in the graph.
- **Uniformity in Lemma 4.1.** A referee should check that `L` and `κ~` are fixed before `d` and `m_j` are
  chosen, and that the orthogonal splitting `XP ⊥ Pπ(a)(1 - P*P)` is exact.

## Literature

- Kun--Thom, arXiv:2608.06222, Theorem E, through the source-verified graph record `kun-thom-nonsofic-wreath`.
- Dogon, arXiv:2211.10492, Definition 1.2 (flexible HS stability), through the graph records.
- Ioana--Spaas--Wiersma, arXiv:2006.01874v2, and Becker--Lubotzky, arXiv:1809.00632: context through the graph
  records of `rf-kazhdan-group-not-flexibly-hs-stable`. They were not re-fetched.
- arXiv:2506.20843v2, "Hyperlinearity, stability and asymptotic spectral gap of higher rank lattices": abstract
  page fetched 2026-09-16. Its content is not relied on.
- F. Fournier-Facio, arXiv:2512.09180, "Stability, approximable quotients, and higher property (T)": abstract
  page fetched 2026-09-16. Its content is not relied on.
- Web search, 2026-09-16, "flexible Hilbert-Schmidt stability property (T) groups arXiv 2025 2026". No
  statement of (H1) over general infranormal pairs was found, and no product-pair counterexample.
- Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Theorem 1.7.11, through the graph record
  `bdhv-central-extension-property-t`.

## Referee (2026-09-16)

**Checked.**
- Read all eight listed files, the target node in full, and the imports `rf-kazhdan-group-not-flexibly-hs-stable`
  (items 1--3), `bdhv-central-extension-property-t` and `kun-thom-nonsofic-wreath` (definition of infranormal,
  Theorem E). `git status` shows no unlisted solver files; `kt-genuine-atomic-vertex-coordinate-models-normalize`
  belongs to another lane.
- **Scope.** The target statement literally quantifies over every infranormal, non-normal pair of Kazhdan groups,
  and two earlier scope bullets already read it that way. `kt-centralizer-normalization-hs` is also general, so the
  two `hs-normalization-via-vertex-rounding-*` routes genuinely used the general form and are correctly left
  invalid. `theorem-e-vertex-unit-type-via-deep-root-mass` used it only at the Theorem E pair, so the restated
  route through the new instance claim is legitimate.
- **Lemmas re-derived by hand.** Lemma 0.1 (block estimate `6(D_n-n)/D_n`), Lemma 0.2 (propagation; uses only
  unitarity of `X_n(x)` and `π'_n(y)`), Lemmas 1.1--1.3, Proposition 2.1 (`P_Γ = Γ_g × P_K`), Lemma 3.1
  (group law, `[x_w,x_u] = z^(2ω(w,u))`, transvection step, finite abelianization; BdHV 1.7.11 discrete form),
  Lemma 4.1 (bimodule `Σ` has `Σ(z) = ζ`, `||P|| = 1`, exact splitting `XP ⊥ Pπ(a)(1-P*P)` since
  `P(1-P*P) = 0`, word bound with `L`, `κ~` fixed before `d`, `D`, `m`), the character computation
  `tr α_k(a) = 0` once `s(a) mod k ∉ <z>`, Lemma 5.1, Theorem 6.1 and Remark 6.3 (`r_n/n < 1/N_(j(n))`).
- **Numerics.** Random-unitary check of the splitting identity in Lemma 4.1 (`d, D` in `{(4,5),(6,9),(10,11)}`):
  cross term `0`, `||β P - Pπ||^2 = ||XP||^2 + ||Pπ(1-P*P)||^2 <= ||X||^2 + (D-d)/d`.
- **Citations.** Fetched arXiv abstract pages 2211.10492 (Dogon, flexible HS stability vs hyperlinearity for (T)
  groups), 2506.20843 (Dogon--Vigdorovich) and 2512.09180 (Fournier-Facio): titles and authors match. The
  numbering "Definition 1.2" of Dogon was not re-verified here (PDF text extraction failed); it is not load-bearing,
  since the refutation covers both the padding and the compression readings.
- **Duplicates.** `cairn search --similar` on both new claims: no existing claim states the product-pair
  refutation or plain (H1) at the Theorem E pair; nearest neighbours are separated by `distinct_from`.

**Changed.**
- Artifact Lemma 1.2: added the triangle-inequality step (almost invariance under `±1` gives it on every finite set).
- Artifact Lemma 0.1: remark that arbitrary unitary padding blocks give the same reading.
- Claim Reading: flagged the `H_2(K; Z) = 0` import (van der Kallen, Quillen) as not source-verified.

**Verdict.** Sound. The general form of (H1) is refuted by an elementary product construction on top of the
established (unreviewed) non-stability of `Z^(2g) ⋊ Sp_(2g)(Z)`; the new content is the amplification-uniform
Lemma 4.1 and the trace-preserving extension to the actor. No novelty is claimed beyond the graph. The Theorem E
instance remains open. Landed with minor fixes.
