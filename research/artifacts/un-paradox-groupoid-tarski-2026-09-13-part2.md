# No invariant measure kills every MF quotient: the groupoid form of the paradox side

Lane `un-paradox` (UN swarm, target U1), 2026-09-13. Part 2.
Part 1 is `un-paradox-stable-infiniteness-2026-09-13.md`, Theorem P: `2n[1] <= n[1]` in `V(R)`
implies no nontrivial MF quotient of `EL_N(R)` for `N >= 2n`. Status: complete written proofs of the
new steps, **unreviewed**. Three imports, each read verbatim from the arXiv PDF on 2026-09-13:
Ara–Bönicke–Bosa–Li (ABBL) arXiv:2001.00376 Lemma 2.3, Rainone–Sims arXiv:1707.04516 Theorem 6.2,
and Elek arXiv:1805.11149 Theorem 1.

## 0. Setting and statements

- `𝒢` is an ample second countable groupoid with compact unit space `X = 𝒢^(0)`.
  - Theorem G assumes `𝒢` Hausdorff, as Import M does.
  - Lemmas 1 and 2, and the family (F2), hold verbatim for non-Hausdorff ample groupoids, where
    `A_k(𝒢)` is the span of indicators of compact open bisections.
- `k` is a countable field, and `A_k(𝒢)` is the Steinberg algebra: in the Hausdorff case, the locally
  constant compactly supported functions `𝒢 -> k` with convolution
  `(f*g)(γ) = sum_(αβ=γ) f(α) g(β)`. Its unit is `1_X`.
- `S(𝒢)` is the type semigroup, in ABBL's presentation (§2): generators `[U]` for compact open
  `U ⊆ X`, subject to `[∅] = 0`, `[A ⊔ B] = [A] + [B]`, and `[s(V)] = [r(V)]` for every compact open
  bisection `V`.

**Theorem G (paradox side).** If `X` carries no `𝒢`-invariant Borel probability measure, then some
`n >= 1` has `2n[1] <= n[1]` in `V(A_k(𝒢))`. So every homomorphism from `EL_N(A_k(𝒢))` to an MF
group is trivial for every `N >= 2n`. If `2[X] <= [X]` in `S(𝒢)`, one may take `n = 1`, so `N >= 2`.

**Corollary F (families).** In each case below `A_k(𝒢)` has a properly infinite unit, so for every
countable field `k` and every `N >= 2`, every homomorphism from `EL_N(A_k(𝒢))` to an MF group is
trivial.
- **Finite `k` (corrected 2026-09-13 after un-verify).** `A_k(𝒢)` is a finitely generated ring, so for
  `N >= 3`, `EL_N(A_k(𝒢))` is a finitely generated Kazhdan group.
- **Infinite `k`.** Neither holds. A finite subset of `EL_N(R)` has entries in a subring with
  coefficients in a finitely generated subring `A ⊊ k`. That `A` is proper because a field finitely
  generated as a ring is finite. So `e_12(λ)` with `λ ∈ k \ A` is not in the subgroup it generates.
  Hence `EL_N(R)` is not finitely generated and has no (T).
- (F1) Boundary actions: `LC(∂F_d, k) ⋊ F_d` for `d >= 2`.
- (F2) Self-similar actions: the Nekrashevych Steinberg algebra of any self-similar action `(G, X)`
  with `G` finitely generated and `|X| >= 2`.
- (F3) Leavitt: `L_k(1,m)` for `m >= 2`, the printed case.

**Headline U1 (one construction, both results).** Take a minimal action `Γ ↷ X` on the Cantor set
and `R = LC(X,k) ⋊ Γ`.
- `Γ = Z` on an infinite minimal subshift (Pestov 9.1): `R` embeds unitally in `prod_ω M_N(F_q)`,
  so `EL_3(R)` is LEF.
- No invariant probability measure: every MF quotient of `EL_N(R)` is trivial from rank `2n`.
- Boundary actions of `F_d`: every MF quotient is trivial from rank 2. Over a finite field `k` the
  group is also finitely generated and Kazhdan from rank 3.

## 1. The type semigroup maps into `V(A_k(𝒢))`

**Lemma 1.** For a compact open bisection `V`, `1_V * 1_(V^(-1)) = 1_(r(V))` and
`1_(V^(-1)) * 1_V = 1_(s(V))`.

*Proof.* `(1_V * 1_(V^(-1)))(γ)` counts pairs `(α, β)` with `α ∈ V`, `β^(-1) ∈ V` and `αβ = γ`.
- Composability gives `s(α) = r(β) = s(β^(-1))`, and `s` is injective on `V`, so `β^(-1) = α`.
- Hence `γ = α α^(-1) = r(α)`, and each unit `x ∈ r(V)` arises from exactly one `α ∈ V`.
- So the function is `1_(r(V))`. The second identity follows by symmetry. QED

**Lemma 2.** There is a monoid homomorphism `Φ : S(𝒢) -> V(A_k(𝒢))` with `Φ[U] = [1_U A_k(𝒢)]`. It
preserves the algebraic preorder, and `Φ[X] = [1]`.

*Proof.* The three relations are checked in turn.
- `[∅] ↦ 0`.
- For disjoint `A, B`, `1_(A⊔B) = 1_A + 1_B` with `1_A 1_B = 0`, so `[1_(A⊔B)] = [1_A] + [1_B]`.
- For a bisection `V`, put `x = 1_V` and `y = 1_(V^(-1))`. Lemma 1 gives `xy = 1_(r(V))` and
  `yx = 1_(s(V))`, and `x = 1_(r(V)) x 1_(s(V))`. So the idempotents `1_(r(V))` and `1_(s(V))` are
  algebraically equivalent, and `1_(r(V)) A ~= 1_(s(V)) A` as right modules.

By the presentation, `Φ` is a well-defined homomorphism. If `y = x + z`, then `Φy = Φx + Φz`, so
`Φ` is monotone for the algebraic preorders. QED

## 2. Tarski

**Import T** (Rainone–Sims, Theorem 6.2, verbatim). "Let (S, +) be an abelian monoid equipped with the
algebraic ordering, and let θ be an element of S. Then the following are equivalent: (i) (n + 1)θ ≰ nθ
for all n ∈ N, that is θ is completely non-paradoxical. (ii) There is a non-trivial state
ν : S → [0, ∞] with ν(θ) = 1." Here a state is an additive, order-preserving map with `ν(0) = 0`.

**Import M** (ABBL, Lemma 2.3, verbatim). "Let G be an ample second countable groupoid. Then each
f ∈ F(S(G)) can be extended to a Borel invariant measure µf ∈ UM(G). Moreover, the restriction of the
measure µf to the open set V := ∪K, where K ranges over all the compact open subsets of G^(0) such that
f([1K]) < ∞, is unique and regular." `F(S)` is the set of monoid homomorphisms `S -> [0,∞]`.

**Lemma 3.** If `X` carries no invariant Borel probability measure, then `2n[X] <= n[X]` in `S(𝒢)`
for some `n >= 1`.

*Proof.*
1. Suppose `ν` is a state on `S(𝒢)` with `ν[X] = 1`. By Import M it extends to an invariant Borel
   measure `μ` agreeing with `ν` on compact open sets, so `μ(X) = 1`, contrary to hypothesis. So no
   such state exists.
2. By Import T, `(k+1)[X] <= k[X]` for some `k >= 1`.
3. Adding `[X]` repeatedly gives `(k+j)[X] <= (k+j-1)[X] <= ... <= k[X]` for all `j`. With `j = k`,
   `2k[X] <= k[X]`. Take `n = k`. QED

This is the step ABBL use in the proof of Proposition 2.11 ("a multiple of [1A] is properly
infinite").

## 3. Proof of Theorem G

- Lemma 3 gives `2n[X] <= n[X]` in `S(𝒢)`.
- Lemma 2 gives `2n[1] <= n[1]` in `V(A_k(𝒢))`, with `A_k(𝒢)` countable because `𝒢` is second
  countable and `k` is countable.
- Theorem P (Part 1) gives the conclusion.
- If `2[X] <= [X]` in `S(𝒢)`, Lemma 2 gives `2[1] <= [1]` directly. QED

No minimality, effectiveness or simplicity is used.

## 4. The families

**(F1) Boundary actions.** Let `F_2 = <a, b>` act on `∂F_2`, the infinite reduced words, and write
`C(g)` for the words starting with the letter `g`. This is the transformation groupoid, and its
Steinberg algebra is `LC(∂F_2,k) ⋊ F_2`.
1. `∂F_2 = C(a) ⊔ C(a^(-1)) ⊔ C(b) ⊔ C(b^(-1))`.
2. Left multiplication by `a^(-1)` maps `C(a)` homeomorphically onto `∂F_2 \ C(a^(-1))`: it deletes
   the leading `a`, and the next letter is not `a^(-1)`.
3. So in `S(𝒢)`: `[C(a)] + [C(a^(-1))] = [∂F_2 \ C(a^(-1))] + [C(a^(-1))] = [X]`, and likewise
   `[C(b)] + [C(b^(-1))] = [X]`. Adding, `[X] = 2[X]`, and Theorem G applies with `n = 1`.

The algebra is generated by `u_a^(±1)`, `u_b^(±1)` and the four `1_(C(g))`. Every cylinder `C(g_1 ... g_m)`
equals `C(g_1) ∩ g_1 C(g_2 ... g_m)`, so by induction its indicator is a product of conjugates
`u_h 1_(C(g)) u_h^(-1)`. Hence the algebra is finitely generated as a `k`-algebra. For finite `k` it is a
finitely generated ring (add the finitely many elements of `k`), and Ershov–Jaikin-Zapirain give (T) for
`N >= 3`. For infinite `k`, see the correction under Corollary F. For `d > 2` use `C(a)`, `C(a^(-1))` for one generator, and the union of the other
cylinders for the second copy.

**(F2) Self-similar actions.** In the groupoid of germs `𝒢_(G,X)` acting on `X^ω`:
- For each letter `x`, the germs of `w ↦ xw` form a compact open bisection `B_x` with
  `s(B_x) = X^ω` and `r(B_x) = C(x)`.
- The `C(x)` partition `X^ω`, so `[X^ω] = sum_x [C(x)] = |X| [X^ω]`.
- With `|X| >= 2` this gives `2[X^ω] <= [X^ω]`, and Theorem G applies with `n = 1`.
- The elements `s_x = 1_(B_x)`, `t_x = 1_(B_x^(-1))` satisfy the Leavitt relations `t_x s_y = δ_xy`
  and `sum_x s_x t_x = 1` (Lemma 1). So the algebra receives `L_k(1,|X|)` unitally, and (PI) is
  visible directly.
- It is generated by the `s_x`, the `t_x` and `1_(germs of g)` for `g` in a finite generating set
  of `G`. So it is finitely generated as a `k`-algebra, and as a ring when `k` is finite.

**(F3) Leavitt.** `L_k(1,m) = A_k(Cuntz groupoid)`. This is the case printed in
`cor:simple-infinite-ring`.

## 5. The boundary of the paradox mechanism

**Firewall K.** Suppose that for some countable field `k` and every countable group `Γ`, whenever
`Γ ↷ X` is a free minimal Cantor action with an invariant probability measure, `LC(X,k) ⋊ Γ` is stably
finite. Then `k[Γ]` is stably finite for every countable group `Γ`. That is Kaplansky's stable
finiteness conjecture over `k`.
- It is known in characteristic 0 (Kaplansky, via traces).
- It is known for sofic groups in every characteristic (Elek–Szabó).
- It is open for general groups in positive characteristic.

So the firewall bites exactly in characteristic `p`. In characteristic 0 the measure side is settled
by a faithful trace (Part 3, Theorem D0).

*Proof.*
- **Import E** (Elek, Theorem 1, verbatim): "For any countably infinite group Γ, there exists a free
  minimal continuous action α : Γ ↷ C on the Cantor set admitting an invariant Borel probability
  measure."
- The map `sum c_g g ↦ sum c_g 1_X u_g` is an injective unital ring homomorphism
  `k[Γ] -> LC(X,k) ⋊ Γ`. Stable finiteness passes to unital subrings: a one-sided inverse in
  `M_m(k[Γ])` is one in `M_m(LC(X,k) ⋊ Γ)`.
- Finite groups have stably finite group algebras, since they are finite-dimensional.

So the measure side of U1's boundary is at least as hard as Kaplansky's stable finiteness conjecture.
No proof that "invariant measure ⇒ no transport mechanism" can avoid it. QED

**What is and is not forced.**
- **Forced.** Every `𝒢` whose Steinberg algebra is not stably finite gives triviality from rank `2n`
  (Theorem P). This includes every no-measure `𝒢` (Theorem G) and every paradoxical `𝒢` from rank 2.
- **Not forced.** Groupoids whose algebra embeds in a matrix ultraproduct (the Pestov ring) give LEF,
  hence MF, groups. No homomorphism to an MF group is forced trivial there, and `EL_3` itself is MF.
- **Open, with a measure.** A minimal effective `𝒢` with an invariant measure whose algebra is not
  stably finite. Firewall K shows that ruling this out is at least as hard as Kaplansky's stable
  finiteness conjecture.
- **Open, low rank.** Triviality for `2 <= N < 2n` in the no-measure case that is not purely infinite
  (the Boldrini–Prasad and Ortega–Perera–Rørdam monoids).
