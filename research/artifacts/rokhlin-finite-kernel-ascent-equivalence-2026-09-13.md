# Ascent of Rokhlin maximality across a finite kernel: an equivalent problem over the quotient, a conditional theorem, and where it stops

Lane `ex-rokhlin-ascent-finite-kernel`, 2026-09-13. Handwritten proofs, nothing computed. Unreviewed.

**Supports:**
- `rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded` (Section 2);
- `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift` (Section 3);
- the Attempts on `rokhlin-maximality-ascends-finite-normal-extensions`,
  `seward-direct-product-relative-rokhlin-entropy-conjecture` and
  `rokhlin-maximality-ascends-amenable-normal-extensions` (Sections 4 and 5).

Notation and imports (I1)–(I4) are those of `research/artifacts/rokhlin-finite-kernel-quotient-formula-2026-09-13.md`
(Part 1), including Theorem QF. Two more imports:
- **(I5) Abért–Weiss** (`abert-weiss-free-actions-weakly-contain-bernoulli`). Every free p.m.p. action weakly
  contains every Bernoulli action, with any base.
- **(I6) Seward, weak containment** (`seward-weak-containment-relative-entropy-equality`, arXiv:1602.06680v2,
  Theorem 1.2). If `X` is free and `Y` is weakly contained in all free p.m.p. actions, then
  `h_G(X | F) = h_G(X × Y | F ∨ B(Y))`.

Say a free ergodic `Q`-action `Y` **lifts** when `Y ≅ X/N` for some free p.m.p. `W`-action `X`. Such an `X` is
ergodic, because a `W`-invariant set is `N`-invariant and hence comes from `Y`.

## 1. The section action

**Definition.** Let `Ω` be the set of sections `σ : Q -> W` with `π σ = id`. Choosing `σ(q)` independently and
uniformly in each coset gives a probability measure `η`. `W` acts by

    (w.σ)(π(w) q) = w σ(q),

which is again a section, since `w` maps the coset `qN` onto `π(w)qN`. `η` is invariant, since each coset is
permuted bijectively.

**Lemma 1.1.**
1. `Ω` is a factor of the Bernoulli shift `[0,1]^W`, hence mixing and weakly contained in every free p.m.p.
   `W`-action.
2. `Ω` is free, `N` acts freely on it, and `h^Rok_W(Ω) <= log n`.
3. `Ω/N` is a free ergodic `Q`-action with `h^Rok_Q(Ω/N) <= n log n + r log n`.

*Proof.* (1) Put `σ_x(q) = argmax_(v ∈ qN) x(v)`, defined a.e. Then
`σ_(w.x)(π(w)q) = argmax_(v ∈ π(w)qN) x(w^-1 v) = w σ_x(q)`. The argmax is uniform in each coset and independent
across cosets, so the push-forward is `η`. Factors of Bernoulli shifts are mixing, and (I5) passes to factors.
(2) Take `w ≠ 1` and `m ∈ N`. If `π(w) = 1`, then `w.σ = σ` fails everywhere. Otherwise, infinitely many disjoint
pairs `{q, π(w)q}` give independent events `w σ(q) = m σ(π(w)q)`, each of probability `1/n`, so `w.σ = m.σ` has
measure `0`. The partition by `σ(1_Q)` generates, because `σ(π(w)) = w (w^-1.σ)(1_Q)`.
(3) Freeness follows from (2) as in Lemma 1.1 of Part 1. Theorem QF gives the bound. QED

**Lemma 1.2 (splitting).** For every finite set `A` there is a `W`-equivariant measure-preserving isomorphism

    A^W × Ω  ≅  Ω × (A^N)^Q,

where `W` acts on `(A^N)^Q` through `Q` by the shift. Hence `(A^W × Ω)/N ≅ Ω/N × (A^N)^Q` as `Q`-actions.

*Proof.* Put `Φ(x, σ) = (σ, d)` with `d(q)(m) = x(σ(q) m)`, inverted by `x(v) = d(π(v))(σ(π(v))^-1 v)`.
- For fixed `σ` this is a relabelling of coordinates `W <-> Q × N`, so product measure goes to product measure.
- `(w.x)((w.σ)(π(w)q) m) = x(w^-1 w σ(q) m) = d(q)(m)`, so `w.(x, σ)` goes to `(w.σ, π(w).d)`.
- `N` acts only on the `Ω` coordinate, which gives the quotient. QED

**Reading.** When the extension splits by a homomorphic section, `Ω/N` is the Bernoulli-type shift `N^Q/N`.
Otherwise the `Q`-action on `Ω/N` is the shift twisted by the extension cocycle. `Ω/N` is where the extension class
lives on the quotient side.

## 2. Theorem B: the ascent is a statement about the quotient

**Theorem B.** Let `W` be countably infinite, `N ◁ W` finite, and `Q = W/N` finitely generated. The following are
equivalent.
- (a) `W` is Rokhlin-maximal at every `q`.
- (b) For every `C` there is a free ergodic `Q`-action `Y` that lifts, with `C < h^Rok_Q(Y) < ∞`.
- (c) For some (equivalently every) finite `A` with `|A| >= 2`, `sup_k h^Rok_Q(Ω/N × ((A^k)^N)^Q) = ∞`.

*Proof.* **(a) ⇒ (c).** Fix `A` and `k`, and put `X = (A^k)^W`.
- **Lower bound over `W`.** By (I6), with `X` free, trivial `F` and `Y := Ω` (Lemma 1.1(1)),
  `h^Rok_W(X × Ω) >= h_W(X × Ω | B(Ω)) = h^Rok_W(X) = k log|A|`.
- **Transfer.** `X × Ω` is free and mixing. By Lemma 1.2 its `N`-quotient is `Ω/N × ((A^k)^N)^Q`. By (2.1) of
  Theorem QF, `h^Rok_Q(Ω/N × ((A^k)^N)^Q) >= n k log|A|`.

**(c) ⇒ (b).** `Y_k = Ω/N × ((A^k)^N)^Q` lifts to `Ω × ((A^k)^N)^Q`, which is free and mixing. By (I1),
`h^Rok_W(Ω × ((A^k)^N)^Q) <= log n + nk log|A|`, so (2.2) of Theorem QF gives `h^Rok_Q(Y_k) < ∞`.

**(b) ⇒ (a).** Let `Y = X/N` with `C < h^Rok_Q(Y) < ∞`. By Theorem QF,
`(C - r log n)/n < h^Rok_W(X) <= h^Rok_Q(Y)/n < ∞`, and `X` is free and ergodic. So `h_sup(W) = ∞`, and (I3)
gives (a). QED

**Remarks.**
1. Theorem B assumes nothing about `Q` beyond finite generation. With Theorem D of Part 1, (a) also implies that `Q`
   is maximal.
2. So the ascent from `Q` to `W` asks whether the small twisted action `Ω/N`, with entropy below `(n + r) log n`,
   can absorb the entropy of arbitrarily large Bernoulli shifts over the maximal group `Q`.

## 3. Corollary C: a conditional ascent

**Corollary C.** Let `Q` be finitely generated and Rokhlin-maximal at every `q`. Suppose some free ergodic `Q`-action
`Y_0` with `h^Rok_Q(Y_0) < ∞` lifts to `W`, and that for some constant `c`

    h_Q(Y_0 × L^Q | B(Y_0)) >= H(L) - c    for uniform bases L of arbitrarily large entropy.     (3.1)

Then `W` is Rokhlin-maximal at every `q`. Condition (3.1) holds with `c = 0` in each of these cases.
- (i) `Y_0` is weakly contained in every free p.m.p. `Q`-action.
- (ii) Some Bernoulli shift `L_0^Q` with `H(L_0) < ∞` lifts to `W`.
- (iii) Seward's direct-product conjecture holds over `Q`: `h_Q(X × Y | B(Y)) = h_Q(X)` for all free p.m.p.
  `X` and `Y`. Here take `Y_0 = Ω/N`.

*Proof.* `Y_k = Y_0 × L_k^Q` lifts: if `Y_0 = X_0/N`, then `Y_k = (X_0 × L_k^Q)/N`, with `L_k^Q` pulled back
through `Q`. It is ergodic, as the product of an ergodic and a mixing action.
- By (I1), `h^Rok_Q(Y_k) <= h^Rok_Q(Y_0) + H(L_k) < ∞`.
- Relative entropy never exceeds absolute entropy, so `h^Rok_Q(Y_k) >= H(L_k) - c`.

Theorem B (b) ⇒ (a) applies.

**The three cases.**
- (i) By (I6) with `X := L^Q` and `Y := Y_0`, `h_Q(Y_0 × L^Q | B(Y_0)) = h^Rok_Q(L^Q) = H(L)`, by maximality of `Q`.
- (ii) `Y_0 = L_0^Q` satisfies (i) by (I5).
- (iii) `Ω/N` is free, has finite entropy (Lemma 1.1) and lifts to `Ω`. QED

**Remark (the co-amenable case, already covered).** Suppose the extension splits over an infinite co-amenable
`Λ <= Q`. Then `π^-1(Λ) = N ⋊ Λ'` with `Λ' ≅ Λ`. It is maximal (a subgroup of `Q`, up finite index) and
co-amenable in `W`. So `W` is maximal by `rokhlin-maximality-ascends-co-amenable-subgroups`, with no appeal to
Theorem B.

## 4. Reductions

**4.1 Central kernels of prime order.** Let `C = C_W(N)`, which has finite index. Then `C ∩ N = Z(N)` is central in
`C`, and `C/Z(N) ≅ CN/N` has finite index in `Q`.
- Maximality of `Q` passes to `CN/N`.
- Maximality of `C` gives maximality of `W` (up finite index).

So ascent for central kernels suffices. By induction on `|N|`, through a central subgroup of prime order, ascent for
central kernels of prime order suffices.

**4.2 The finite case is inside the split locally finite case.** By the Kaloujnine–Krasner embedding, `W` embeds in
the unrestricted wreath product `N^Q ⋊ Q`, compatibly with the maps to `Q`. Let `C` be the countable `Q`-invariant
subgroup of `N^Q` generated by the base components of the image of `W`.
- `C` lies in the variety generated by the finite group `N`, which is locally finite. So `C` is amenable.
- `W <= C ⋊ Q`, and `(C ⋊ Q)/C = Q`.

So ascent across split, locally finite kernels gives the finite-kernel ascent, through subgroups. The Kun–Thom wreath
has exactly the split, locally finite shape. So `rokhlin-maximality-ascends-amenable-normal-extensions`, even
restricted to that shape, contains the finite case.

## 5. Where an unconditional proof stops

This section is a mechanism analysis, not a theorem.

1. **Only weak containment transfers lower bounds without finite models.** In the sources read, the model-free
   lower-bound tool is (I6) and its stabilizer-type form (Seward, Theorem 6.5). Its proof uses, for a small-entropy
   factor `Z` of `X` with the same stabilizers, a weak containment of joinings `X × Z ≽ X × Y` (Corollaries 5.2 and
   6.4(4)). So over `Q`, a liftable `Y_0` must be approximately simulable inside factors of Bernoulli shifts.
2. **For `Ω/N` this is cohomological (sketch).** A `Q`-equivariant map from a Bernoulli shift `B^Q` onto `Ω/N`
   assigns to almost every point a section modulo `N`, equivariantly. Comparing the sections at `d` and `q.d` gives
   a measurable lift of the extension cocycle on the orbit relation of `B^Q`. Conversely, such a lift joined with
   independent uniform labels in `N` should give a factor map from `B^Q × N^Q` onto `Ω/N`; this is not written out.
   So case (ii) of Corollary C asks whether the extension class dies on a Bernoulli orbit relation, and case (i) for
   `Ω/N` asks for an approximate version.
3. **Rigid extensions.** Gohla–Thom, as recorded on `gohla-thom-stable-base-nonsofic-extension` (arXiv:2403.09582v2,
   Theorem 3.13), prove the following. Let `Γ` be residually finite of finite type with a cosystolic inequality, and
   let it carry a non residually finite central extension. If `Γ` is stable in finite actions, the extension is
   nonsofic. Their engine is an obstruction `θ^P_*(α)`:
   - it vanishes on limit actions of sofic approximations of the extension (their Theorem 3.4);
   - under the cosystolic inequality, it is nonzero on actions weakly contained in finite actions (their
     Theorem 2.16).

   Not re-read from the source here.
   - Not checked here: whether `θ` vanishes on every liftable action.
   - If it does, then over such `Γ` no liftable action is weakly contained in finite actions, and Corollary C(i) would
     need `Ω/N ≺ L^Q` while `L^Q` itself is not weakly contained in finite actions.

   These are exactly the extensions where soficity is expected to fail.
4. **What a counterexample needs** (from Theorem B, Corollary C and Section 3). A finite extension `W` of a maximal
   `Q` that is not maximal must satisfy all of the following:
   - `W` is nonsofic;
   - the extension is non-split on every infinite co-amenable subgroup of `Q`;
   - no liftable free action of finite entropy is weakly contained in all free `Q`-actions, and no Bernoulli shift of
     `Q` lifts;
   - Seward's direct-product conjecture fails over `Q`, on the pairs `(((A^k)^N)^Q, Ω/N)`, with bounded
     `h^Rok_Q(Ω/N × ((A^k)^N)^Q)`.
5. **Contrast with infinite amenable kernels.** For the lamp kernel of the Kun–Thom wreath, information fixed by the
   kernel has zero outer entropy (`infinite-subgroup-invariant-information-has-zero-outer-entropy`). For a finite
   kernel, Theorem QF says the `N`-quotient carries all of the entropy, to within `(r log n)/n`. So the finite case is
   a problem about lifting the extension class, not about Følner counting along the kernel. The two neighbour lanes
   face different obstructions.

## 6. Literature check (bounded)

Read 2026-09-13 from PDF texts extracted on MSI (`review-lit/entropy/`, and `ex/ex-rokhlin-lower/` for 1705.09707 and
1804.05270):
- Alpeev–Seward, arXiv:1705.09707: introduction pp. 1–6 and the proof of Theorem 1.11 in Section 9;
- Seward, arXiv:1602.06680v2: introduction and Sections 4–6;
- Seward, arXiv:1405.3604, 1501.03367v4, 1804.05270v1 and 1805.08279v1: keyword searches for normal subgroups,
  quotients, extensions and finite index.

**Found.**
- The quotient remark: "If G y (X;µ) is a p:m:p: action and G is a quotient of Γ, then Γ acts on (X;µ) by factoring
  through G, and it is easily checked that hRok_Γ(X;µ) = hRok_G(X;µ)."
- Theorem 1.11 of 1705.09707.
- In 1602.06680 the subgroup formula is open for nonamenable groups, and of the product equality Seward writes: "is
  known to hold when G is amenable but is unknown otherwise".

**Not found.** A quotient formula for finite normal subgroups, descent or ascent of INF along finite kernels, or the
section action.

**Not checked.** Seward's Sinai factor paper (arXiv:1804.05269), Hayes's relative sofic entropy papers, surveys. The
web search budget was exhausted. Novelty is therefore unreviewed.

## 7. Addendum (same day): the checkable sufficient conditions, tested

1. **Bernoulli lifting is excluded over w-rigid quotients.** `bernoulli-lifts-across-finite-kernels-force-virtual-splitting`
   (complete proof in its route).
   - The lifting cocycle `c(γ, x) ∈ π^-1(γ)` of a torsor over a diffuse Bernoulli shift is a `W`-valued cocycle.
   - Popa's Theorem 0.1 (arXiv:math/0512646v8, p. 4) makes it cohomologous to a homomorphism `δ`.
   - Projecting to `Q`, the conjugator pushes `μ` forward to an invariant probability measure for
     `γ . g = γ g θ(γ)^-1`. So `θ = π δ` is conjugation by some `g` on a finite-index `Q_0`, and `ĝ δ ĝ^-1` splits the
     extension over `Q_0`.
   - So case (ii) of Corollary C covers only virtually split extensions when `Q` is w-rigid, for example `Sp_4(Z)`.
   - The relative form of Popa's theorem (cocycles of `σ × ρ` come from `ρ`) is consistent with the liftability of
     every product `L^Q × Y_0` with liftable `Y_0`.
2. **Property MD.** Seward, arXiv:1602.06680v2, Corollary 8.8, read 2026-09-13: "Let G be a residually finite group
   with property MD, let G y (X;µ) be an aperiodic p:m:p: action, and let F be a G-invariant sub-σ-algebra with
   hG(X;µ|F)<∞. The following are equivalent. (1) hG(X;µ|F) = hG(X×Y;µ×ν|F∨B(Y)) for all p:m:p: actions G y (Y;ν).
   (2) [subgroup formula]. Furthermore, if Σ is a soﬁc approximation to G with hΣ_G(G/∆;u_{G/∆}) ≠ −∞ for every
   ﬁnite-index normal subgroup ∆◁G and hΣ_G(X;µ) = hG(X;µ) < ∞, then (1) and (2) hold with F = {∅;X}."
   - For residually finite `Q`, take `Σ` through the quotients by the intersections of all normal subgroups of index
     at most `i`. The quotient maps give exact models of every finite action, and `X = L^Q` has
     `h^Σ = h^Rok = H(L)`.
   - So (1) holds for `Y = Ω/N`, and Corollary C(iii) gives ascent for every finite extension of an MD group.
   - **Scope.** The same page says "SLn(Z) has property MD precisely when n = 2", because property FD fails for
     `n > 2`. The MD examples listed there are good groups, whose finite central extensions virtually split.
3. **Weak containment of `Ω/N` in finite actions.** Seward's Lemma 8.5 and Theorem 8.7 give
   `h_Q(L^Q × Y | B(Y)) >= h^Σ(L^Q)` for finitely modular `Y`. So `Ω/N ≺ Z` for one finitely modular `Z` also gives
   (3.1), through Corollary 6.4(4).
   - Heuristic, not proved: such a weak containment reads approximate lifts on finite quotients `Q/Δ`, hence sofic
     approximations of `W`, so it would be a sofic-level hypothesis.
   - This is where Gohla–Thom's obstruction lives: under a cosystolic inequality, actions weakly contained in finite
     actions carry a nonzero class.

**Net.** The model-free sufficient condition left open is weak containment of `Ω/N` in Bernoulli shifts of `Q`, not in
finite actions. Equivalently, it is Seward's direct-product equality for the pairs `(L^Q, Ω/N)`.
