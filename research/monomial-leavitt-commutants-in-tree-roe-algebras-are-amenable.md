---
rg: 2
id: monomial-leavitt-commutants-in-tree-roe-algebras-are-amenable
kind: claim
title: In the translation algebra of a tree, the relative commutant of every monomial copy of L maps unitally to the translation algebra of its grand-orbit space, and that space is amenable, so the commutant contains no Leavitt algebra; so every copy of L⊗L in K_u(tree), and every leg of any L_2⊗L_2 ↪ L_2, is non-monomial
requires:
  - lamplighter-canonical-algebra-embeds-in-leavitt-tensor-square
  - non-amenable-scaffolds-absorb-the-leavitt-factor
distinct_from:
  lamplighter-canonical-algebra-embeds-in-leavitt-tensor-square: that shows K[Z²] has no monomial module over a tree, so two commuting monomial Thompson shifts are impossible; this computes the full relative commutant of one monomial Leavitt copy (a Morita-type invariant) and shows it contains no unital Leavitt algebra, so even ONE monomial leg is impossible.
  non-amenable-scaffolds-absorb-the-leavitt-factor: that decides when K_u(P) or a crossed product contains L; this decides when the COMMUTANT of a monomial L contains L, by applying the Ara–Li–Lledó–Wu dichotomy to a derived space.
---

**ESTABLISHED** (lane proof, bh-algebra; elementary given the cited results; not reviewed; no priority claimed).

Cited:
- Ara–Li–Lledó–Wu, arXiv:1607.00328, Theorem 6.3 (read at source, 09-18). For a locally finite extended
  metric space `Q` and a field `K`, the following are equivalent:
  - `Q` is amenable;
  - `K_u(Q)` is algebraically amenable;
  - `K_u(Q)` is not properly infinite;
  - `K_u(Q)` contains no unital `L_K(1,n)`.
  Their proof of (4) ⇒ (1) builds `L` from a paradoxical pair of partial translations.
- Chen's modules `V_[p]` over `L` (Chen, J. Algebra 2015; recalled). The two facts used are re-proved below.

**Setting.** `X` is a connected graph of bounded degree and `K` a field. `K_u(X)` is the translation algebra,
the span of the operators `V_t` of partial translations on `ℓ(X) = K^(X)`. A unital copy of `L = L_K(1,2)` in
`K_u(X)` is **monomial** if `x_1, x_2, y_1, y_2` act by partial permutations of the basis.

## Lemma 1 (monomial copies are 2-to-1 maps)

Monomial unital copies of `L` correspond exactly to pairs of injections `f_1, f_2 : X → X`, of bounded
displacement and with images partitioning `X`, via `x_i = V_(f_i)` and `y_i = V_(f_i)^(-1)`.

*Proof.* From `y_i x_i = 1`, `x_i` is an injective partial permutation, hence a total injection `f_i`. The
column of `y_i` at `f_i(v)` then occupies row `v`, which forces `y_i = V_(f_i)^(-1)`. Next, `y_1 x_2 = 0` makes
the images disjoint, and `x_1 y_1 + x_2 y_2 = 1` makes them cover `X`. Finite propagation gives bounded
displacement. ∎

Write `φ` for the 2-to-1 map with `φ ∘ f_i = id`.
- A **grand orbit** is a class of `v ~ w ⟺ φ^m v = φ^n w`.
- The **address** of `v` is the sequence `a_1 a_2 ⋯` with `φ^(k−1)v = f_(a_k)(φ^k v)`.

## Lemma 2 (the three kinds of grand orbit)

Each grand orbit `c` has all of its addresses in one tail class `[p_c]`, and it is of exactly one of three
kinds.
- **Aperiodic.** `p_c` is not eventually periodic.
- **Cycle.** `φ` has a periodic cycle in `c`.
- **Line.** `p_c ~ c^∞` is periodic, there is no cycle, and `c` contains a bi-infinite chain `z_(k+1) = f_c(z_k)`,
  `k ∈ Z`, of points with address exactly `c^∞`.

For the first two kinds, the address map is a bijection onto `[p_c]`, and `K^(c)` is Chen's module `V_[p_c]`:
`x_i` prepends `i`, and `y_i` deletes a leading `i` or kills. For a line, the address map is `Z`-to-1, and the
deck bijection `τ(f_α z_k) = f_α z_(k+1)` commutes with `L`.

Module maps between grand orbits:
1. `Hom_L(K^(c'), K^(c))` is zero unless `c, c'` have the same tail class and the same kind.
2. For two orbits of one of the first two kinds, it is `K·Θ`, with `Θ` the address-preserving bijection.
3. For two lines, it is `span{Θ τ^k : k ∈ Z}`, with `Θ(z'_0) = z_0`.

*Proof.*
1. Every orbit module is cyclic on a point `v`: `e_(f_α φ^m v) = x_α y_(β) e_v` for suitable words.
2. A module map `T` commutes with the idempotents `x_α y_α`. So `T e_v` is supported on points whose address has
   every prefix of `address(v)` as a prefix, that is, on points with the same address as `v`.
3. In a Chen-type orbit there is exactly one such point, which gives `K·Θ`. In a line, when `address(v) = c^∞`,
   these points are the `z_k`, which gives `Σ λ_k Θ τ^k`.
4. Across kinds, write `w` for the unique point of the cycle orbit with address `c^∞`; it is fixed by `f_c`.
   - A map from a line to a cycle orbit sends every `z'_k` to a multiple of `e_w`. It then has infinitely
     many entries in row `w`, so it is not of finite propagation, unless it is zero.
   - A map from a cycle orbit to a line sends `e_w = x_c e_w` to a finite vector that is invariant under the
     shift `z_k ↦ z_(k+1)`, which must be `0`.
   - Aperiodic and periodic tail classes never meet. ∎

## Theorem 1 (the relative commutant)

Let `Q_φ` be the set of grand orbits. Put `d(c, c') = min_Θ sup_(v∈c') d_X(v, Θ v)`, the minimum over the
`L`-equivariant bijections `Θ : c' → c` (`∞` if there are none). This is a locally finite extended metric
space: `c'` within `R` of `c` meets the `R`-ball of a fixed point of `c`, and grand orbits are disjoint. Write
`C = L_φ' ∩ K_u(X)`.
1. `C = C_0 ⊕ C_line` centrally, split by orbit kind.
2. `C_0 ≅ K_u(Q_0)`, via `Σ λ_(cc') Θ_(cc') ↔ (λ_(cc'))`, where `Q_0` is the set of aperiodic and cycle orbits.
3. On lines, fix base points `z^c_0` with compatible `Θ`'s. Then `C_line` is the algebra of matrices over
   `Q_line` with entries `Σ λ_k t^k ∈ K[t^(±1)]`, subject to the propagation bound. Evaluation at `t = 1` is a
   unital homomorphism `ε : C_line → K_u(Q_line)`.
4. So `ε = id ⊕ ev_1 : C → K_u(Q_φ)` is a unital homomorphism. Moreover, every partial translation `t` of
   `Q_φ` lifts to a monomial element `Σ_c Θ_(t(c),c)` of `C`, choosing on lines the `Θ` that attains the
   minimum.

*Proof.* `ℓ(X) = ⊕_c K^(c)`, and `T ∈ C` exactly when every block is a module map. Lemma 2 gives the forms and
the splitting. Propagation is the sup over the nonzero terms of the displacement of `Θτ^k`, since distinct
`k` hit distinct points. The finitely-many-values condition matches. Composition matches because the `Θ`'s are
compatible and `τ` commutes with them. `ev_1` is a ring map on the entries, and the lifts are equivariant
partial bijections. ∎

## Theorem 2 (over a tree the commutant contains no Leavitt algebra)

Let `X` be a tree of bounded degree, or any bounded-degree graph with `sep_X(m) = o(√m)`, and let `L_φ ⊆ K_u(X)`
be a monomial unital copy. Then `Q_φ` is amenable. The commutant `C` contains no unital `L_K(1,n)` for any
`n ≥ 2`, so it is not properly infinite. When there are no lines, `C ≅ K_u(Q_φ)` is algebraically amenable.

*Proof.*
1. Suppose `Q_φ` is not amenable. By Ara–Li–Lledó–Wu there are partial translations `t_±` onto a partition
   `Q_+ ⊔ Q_-`. They preserve kinds, since distances across kinds are `∞`.
2. By Theorem 1(4) they lift to injective partial permutations `X_± ∈ C` with complementary images, hence to a
   monomial unital `L' ⊆ C` (Lemma 1).
3. `L_φ` and `L'` then generate `L ⊗ L`, which is simple and acts faithfully on `ℓ(X)`. For `g ∈ V` of
   infinite order, `g ⊗ 1` and `1 ⊗ g` are commuting permutations of bounded displacement generating a
   faithful `K[Z²]`.
4. This contradicts Theorem 2 of `lamplighter-canonical-algebra-embeds-in-leavitt-tensor-square`. So `Q_φ` is
   amenable.
5. If `C` contained a unital `L_K(1,n)`, its image under `ε` would be one in `K_u(Q_φ)`: it is injective,
   because `L_K(1,n)` is simple and `ε` is unital. Ara–Li–Lledó–Wu (1) ⇒ (4) excludes this, and (1) ⇒ (2) gives
   the last sentence. ∎

Matrix amplifications are covered: `M_n(K_u(X)) = K_u(X × [n])`, and the proof is unchanged.

## Corollaries

1. **Both legs of any `L ⊗ L` in a tree algebra are non-monomial.** If `L ⊗ L` embeds unitally in
   `M_n(K_u(X))` for a tree `X`, then neither `L ⊗ 1` nor `1 ⊗ L` is a monomial copy.
   - Contrast the product of trees: `X_par × X_par` gives a monomial `L ⊗ L` in `K_u(F_2 × F_2)`, and there
     `Q_(φ × id)` contains copies of the second tree, so it is non-amenable.
2. **The Brownlowe–Sørensen problem, over every field.** Let `ψ : L_K ⊗ L_K → L_K` be a unital embedding.
   Compose with `L_K ⊆ K_u(F_2)`. The monomial copies of `L` in `K_u(F_2)` then include every "prefix-code"
   copy `x_i ↦ w_i`, where the `w_i` are monomial isometries `Σ x_α y_β` with complementary ranges.
   - So no leg of `ψ` is a prefix-code copy.
   - This is a leg-level companion to Brownlowe–Sørensen's obstruction via Thompson's group `V`
     (arXiv:1603.03618).
3. **For gate U.** The one-tree Kirchberg problem for `R_1` needs a non-monomial `L` whose commutant in
   `K_u(F_2)` is properly infinite. The commutant of a monomial copy is always a *geometric* translation
   algebra, up to Laurent coefficients on periodic lines, and over a tree an amenable one.

## Lesson for general BH

ALLW's amenability dichotomy has a relative version.
- The commutant of a dynamically built (monomial) Leavitt copy is again a translation algebra, now of the
  space of its grand orbits (up to Laurent coefficients on periodic lines).
- Over one tree that space is always amenable, so a second commuting copy can never come from dynamics.

This is the Morita-type invariant behind "one tree versus two".
- `O_2 ⊗ O_2 ≅ O_2` needs genuinely linear, non-monomial Leavitt copies. The C*-proof supplies them by
  approximation, which has no algebraic analogue here.
- Track B loses nothing, because its scaffold can be `F_2 × F_2`, which is finitely presented and
  Farrell–Jones, where `L ⊗ L` and `R_1` are monomial.
- The sharp next question is therefore over a fixed product of trees: does `R_Z`, which contains `K[Z^n]`
  for every `n`, embed in `K_u(F_2 × F_2)`?
