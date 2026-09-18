---
rg: 2
id: boolean-inverse-monoid-finite-presentation-is-finite-type-proof
kind: route
title: Build the additive map out of the bisection monoid from the canonical λ-decomposition and Stone duality; for the converse, map into the finite-type approximations and read off the dual map
target: boolean-inverse-monoid-finite-presentation-is-finite-type
---

Notation is that of the target. For `λ ∈ Λ` let `δ_λ = {(λ, x) : x ∈ X}` (the unit `x -> λ.x`), and for a
clopen `f ⊆ X` write `f δ_λ` for the product, the bisection `{(λ, x) : λ.x ∈ f}` from `λ^(-1).f` to `f`. Write `[a]_h = {x : x(h) = a}`.

## 0. Two facts about B(𝒦)

- **Canonical form.** Every compact open bisection `b` of `𝒦` is uniquely `b = ⊕_λ b_λ δ_λ`, with
  finitely many nonempty clopens `b_λ`, where `b_λ` is the set of ranges of arrows of `b` labelled `λ`.
  - The `b_λ` are pairwise disjoint, and so are the sources `λ^(-1).b_λ`.
  - Compactness gives finiteness. The label of an arrow `(λ, x)` is part of the arrow, so no freeness is
    needed.
- **Calculus.**
  - `(f δ_λ)(g δ_μ) = (f ∩ λ.g) δ_(λμ)`, since `δ_λ g = (λ.g) δ_λ`.
  - `δ_λ [a]_h δ_λ^(-1) = [a]_(λh)`.
  - `(f δ_λ)^(-1) = (λ^(-1).f) δ_(λ^(-1))`.

## 1. Part 1 for B(𝒦)

**Generation.**
- `δ_λ` is a product of the `δ_s`, and `[a]_h = δ_h [a]_1 δ_h^(-1)`.
- Every clopen of `X` is a finite disjoint union of finite intersections of cylinders. Intersections
  are products of idempotents, disjoint unions are orthogonal joins, and `[a]_h^c = ⊕_(b ≠ a) [b]_h`.
- So the canonical form writes every bisection from `δ_s` and `[a]_1`.

**The relations hold** under `u_s -> δ_s`, `e_a -> [a]_1 δ_1`.
- (U) and (P) are clear.
- For (F), the product is `∩_w [α(w)]_w`, which is the set of `x` containing `α` at the identity. It
  is empty because `α` is forbidden.

**Universal property.** Let `N` be a Boolean inverse monoid, with `u_s -> ρ_s` and `e_a -> p_a`
satisfying (U), (P) and (F).
1. By (U), `s -> ρ_s` extends to a homomorphism `ρ : Λ -> U(N)`.
2. **The Boolean algebra map.**
   - Let `𝔅` be the Boolean algebra with generators `c_(a,h)` (`a ∈ A`, `h ∈ Λ`) and relations
     `c_(a,h) c_(b,h) = 0` (`a ≠ b`), `⋁_a c_(a,h) = 1`, and `⋀_(w ∈ W) c_(α(w), hw) = 0` for
     `α ∈ 𝔽`, `h ∈ Λ`.
   - Its Stone space is the set of `x ∈ A^Λ` avoiding every translate of every `α ∈ 𝔽`. That set is `X`.
   - A Boolean algebra is the algebra of clopens of its Stone space, so `c_(a,h) -> [a]_h` is an
     isomorphism `𝔅 ≅ Clopen(X)`.
   - In the Boolean algebra `E(N)` put `q_(a,h) = ρ(h) p_a ρ(h)^(-1)`. Conjugating (P) and (F) by
     `ρ(h)` shows the `q_(a,h)` satisfy the relations of `𝔅`. For (F) at translate `h`,
     `ρ(h) (∏_w ρ(w) p_(α(w)) ρ(w)^(-1)) ρ(h)^(-1) = ∏_w q_(α(w), hw) = 0`.
   - So there is a Boolean homomorphism `π : Clopen(X) -> E(N)` with `π([a]_h) = q_(a,h)`.
   - It is covariant: `π(λ.f) = ρ(λ) π(f) ρ(λ)^(-1)`. Both sides are Boolean homomorphisms in `f` and
     agree on cylinders.
3. **The extension.** Define `Φ(⊕_λ b_λ δ_λ) = ⊕_λ π(b_λ) ρ(λ)`.
   - The terms are orthogonal. The range of `π(b_λ) ρ(λ)` is `π(b_λ)` and its domain is
     `π(λ^(-1).b_λ)`, and covariance transports the disjointness of the canonical form. So the join
     exists.
   - `Φ` is multiplicative on the terms `f δ_λ`, by covariance:
     `π(f) ρ(λ) π(g) ρ(μ) = π(f ∩ λ.g) ρ(λμ)`, which is `Φ` of the product.
   - Products distribute over orthogonal joins in a Boolean inverse monoid, so `Φ` is multiplicative.
     It preserves joins, inverses, 0 and 1.
   - It sends `δ_s -> ρ_s` and `[a]_1 -> p_a`.

`∎` (part 1 for `𝒦`).

## 2. Part 1 for B(T)

- **Monomials.** For finite words `w, w'`, let `Z(w, w')` be the compact open bisection
  `{(wc, |w| - |w'|, w'c)}` of `G_V`, and `y_w = x_(w_1) ... x_(w_k)`. Then `Z(w, w') = y_w y_(w')^(-1)`.
- **Canonical form.**
  - Products `Z(w, w') × b`, with `b ∈ B(𝒦)`, form a basis of compact open bisections of `T` that is
    closed under intersection.
  - Given a bisection `B` of `T`, choose `d` larger than the words in some finite cover of `B`. Then
    `B = ⊕_(|w'| = d, w) Z(w, w') × b_(w,w')`.
  - For an arrow of `B`, `w'` is the length-`d` prefix of its source and `w` is read off its range and
    lag. So the pieces are determined, and the form is unique at depth `d`.
  - Passing from depth `d` to `d+1` replaces `Z(w, w') × b` by `⊕_i Z(wi, w'i) × b`.
- **Universal property.** Let `N` and images satisfying (U)(P)(F)(C)(M) be given.
  - §1 gives `Φ_𝒦 : B(𝒦) -> N`. The `ξ_i` (images of `y_i`) satisfy the Cuntz relations.
  - By (M), `ξ_w` and `ξ_w^(-1)` commute with every element of `Φ_𝒦(B(𝒦))`. They commute with the
    images of the `u_s` and `e_a`, the `u_s` are units, and commutation passes to products, inverses and
    joins.
  - Define `Φ(⊕ Z(w, w') × b_(w,w')) = ⊕ ξ_w Φ_𝒦(b_(w,w')) ξ_(w')^(-1)`.
    - **Independent of `d`.** Insert `1 = ⊕_i ξ_i ξ_i^(-1)` and commute: the result is
      `ξ_w Φ(b) ξ_(w')^(-1) = ⊕_i ξ_(wi) Φ(b) ξ_(w'i)^(-1)`.
    - **Orthogonal.** Sources with different `w'` of equal length are orthogonal, because
      `(ξ_0 ξ_0^(-1))(ξ_1 ξ_1^(-1)) = 0`. When one `w` is a prefix of another, the ranges are orthogonal
      because `B` is a bisection, which forces the `𝒦`-ranges to be disjoint.
    - **Multiplicative.** It is multiplicative on monomials by the Cuntz calculus: `ξ_u^(-1) ξ_v` is
      `ξ_(v')`, `ξ_(u')^(-1)` or `0` according to the prefix relation of `u` and `v`. That is the rule
      for `Z` products.

`∎` (part 1 for `T`).

## 3. Part 2

Let `Λ` be finitely generated with finite symmetric generating set `S`, and suppose `B(𝒦)` is
finitely presented.

1. **Tietze.** `Σ' = {δ_s} ∪ {[a]_1}` generates `B(𝒦)` (§1). Boolean inverse monoids, in the
   orthogonal-join signature, form a variety (Wehrung, recalled). So `B(𝒦)` is presented on `Σ'` by a
   finite set `R'` of term equations, including any orthogonality side conditions needed for joins.
   - Explicitly: express the old generators as terms `t_σ` in `Σ'` and the elements of `Σ'` as terms
     `s_(σ')` in the old generators. Take `R'` to be the old relations rewritten through the `t_σ`, plus
     `σ' = s_(σ')(t_σ)`.
   - The universal property on `Σ'` then follows from the old one.
2. **Relations are local.** Let `Y` be any `Λ`-subshift, and evaluate a term in `δ_s`, `[a]_1` inside
   `B(Λ ⋉ Y)`.
   - The result is a bisection `⊕ b_λ δ_λ` whose finitely many clopens are unions of cylinders on a
     finite window `F`, fixed by the term.
   - So an equation `t = t'` holds in `B(Λ ⋉ Y)` iff no `F`-pattern in the language `L_F(Y)` lies in a
     finite "bad" set determined by `t, t'`.
3. **Approximations.** Let `X_N` be the set of `y ∈ A^Λ` all of whose translated `B_N`-patterns occur
   in `X`.
   - `X_N` is an SFT containing `X`.
   - `L_F(X_N) = L_F(X)` once `B_N` contains a translate of `F`.
   - Since `R'` holds in `B(𝒦)`, step 2 shows `R'` holds in `B(Λ ⋉ X_N)` for all large `N`.
4. **The map.** The universal property gives an additive `Θ : B(Λ ⋉ X) -> B(Λ ⋉ X_N)` with
   `Θ(δ_s) = δ_s` and `Θ([a]_1) = [a]_1`, hence `Θ([a]_h) = [a]_h` for all `h`.
   - On idempotents, `Θ` is a Boolean homomorphism `θ : Clopen(X) -> Clopen(X_N)` sending each
     cylinder of `X` to the same-named cylinder of `X_N`.
   - Let `α` be a pattern on a window `U` that does not occur in `X`. Then `∩_(u ∈ U) [α(u)]_u = ∅` in
     `X`, so its `θ`-image `∩_(u ∈ U) [α(u)]_u` is empty in `X_N`, and `α` does not occur in `X_N`.
   - So `L(X_N) ⊆ L(X)`, which gives `X_N ⊆ X`, and `X = X_N` is of finite type.

For `B(T)`, run the same argument with `Σ' ∪ {y_0, y_1}` and `G_V × (Λ ⋉ X_N)`. The `G_V`-part is
unchanged, so relations are still decided by bounded `X`-windows, and the idempotent map still sends
`C × [a]_h` to `C × [a]_h`. `∎`

**Remark (where rigidity went).**
- The relation set (F) mentions only finitely many idempotents, yet the presented object "knows" that
  `u_λ e_a u_λ^(-1)` and `e_b` commute for every `λ`. That knowledge is built into the axioms of a
  Boolean inverse monoid, since `E(N)` is a Boolean algebra.
- A presentation of the group `U(B)` or of the algebra `k B` has no such axiom. That missing axiom is
  exactly the commutation that `sft-crossed-product-fp-iff-quantum-rigid` and
  `fp-v-times-subshift-full-groups-force-quantum-rigidity` show must be *derived*.
