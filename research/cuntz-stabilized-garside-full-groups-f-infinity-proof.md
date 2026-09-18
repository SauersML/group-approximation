---
rg: 2
id: cuntz-stabilized-garside-full-groups-f-infinity-proof
kind: route
title: Pure-hole cylinders of the product with the free monoid on two letters satisfy Li's (St) and (LCM); the Cuntz doubling move gives packing at least the piece count, and (Acyc) gives a height, so Witzel's criterion applies
target: cuntz-stabilized-garside-full-groups-are-f-infinity
requires:
  - perron-weights-do-not-give-li-finiteness
  - perron-weights-do-not-give-li-finiteness-proof
  - thin-cycles-decide-li-packing
---

**Lane proof, not independently reviewed.** Labels are Li's (arXiv:2110.04505v2). Notation:
- `M = ⟨x,y⟩` is the free monoid, and `𝔠₂ = 𝔠 × M` has objects `𝔠⁰`.
- `𝔖₂ = (𝔖^♯ × {1,x,y}) ∖ {units}`, where `𝔖^♯ = 𝔖 ∪ 𝔠⁰`.
- `X₂ = X × {x,y}^ℕ`.

## 1. Li's hypotheses for `𝔠₂`

All hold componentwise.
- `M` is free: cancellative, trivial units, and `wM ∩ w'M` is `∅` or principal.
- For `𝔠₂`: `(a,w)𝔠₂ ∩ (b,w')𝔠₂ = (a𝔠 ∩ b𝔠) × (wM ∩ w'M)`, a disjoint union of
  principal ideals. So `𝔠₂` is finitely aligned with disjoint mcms, right Noetherian and
  cancellative up to `=*`, and (F) holds.

**Garside family.** Take the `𝔖`-normal form `s_1⋯s_n` of `a` and the letters
`t_1⋯t_m` of `w`, and pad the shorter one with identities. Then `(s_i, t_i)` is an
`𝔖₂`-normal form of `(a,w)`:
- the largest `𝔖₂^♯`-divisor of a pair is the pair of the largest divisors;
- Li's normality condition holds in each coordinate.

Moreover:
- `𝔖₂` is locally finite, with three choices of letter;
- `‖(a,w)‖ = max(‖a‖, |w|)`;
- `(𝔖₂^{≤L})^♯ = (𝔖^{≤L})^♯ × M_{≤L}` is closed under left divisors;
- `𝔖^♯` is closed under mcms and right divisors, and so is `𝔖₂^♯`.

**Boundary.** Constructible ideals of `𝔠₂` are finite disjoint unions of products, so
`Ω(𝔠₂) = Ω(𝔠) × Ω(M)`. Then:
- `X₂` is closed, invariant and contained in `Ω_∞(𝔠₂)`;
- `I_l(𝔠₂) ⋉ X₂ ≅ 𝒢 × G_2`.

This is the observation Li makes in the proof of `cor:ProdGraphs`.

## 2. The pure-hole datum

**Types and moves.**
- A type `X₂(v;e)` (`e ⊆ v𝔖₂`) is **pure** if `e ⊆ 𝔖 × {1}`. As a set it is
  `(X(v;e_𝔠) ∩ X) × {x,y}^ℕ`.
- Let `𝔛` be the nonempty pure types. There are finitely many, since `v𝔖` is finite.
- Let `𝚪` be the elements of Li's one-layer set `𝐒` (for `𝔠₂`) whose target pieces and
  domain pieces are all pure.
- Let `Γ ⊆ 𝚪` be those with a single target piece.

Li's own maximal datum (`lem:maxXG:allCOND`) takes `𝚪 = 𝐒`, so multi-target one-layer
elements are allowed.

**Lemma P.** Let `X₂(v;e)` be pure and `𝔰 = (A × B) ∖ {(1,1)}`, with `A ⊆ v𝔖^♯` and
`B = {1}` or `B = {1,x,y}`. Then every nonempty piece of `γ(e,𝔰)`, the leftover included,
is pure.

*Proof.* For `s = (p,t)` the holes `𝔣_s` are the minimal `f = (f_𝔠, f_M)` with
`sf ∈ 𝔰` or `sf ∈ mcm(s,e)`.
- **`t ∈ {x,y}`.** `tf_M ∈ B` forces `f_M = 1`. Also
  `mcm((p,t), (q,1)) = mcm_𝔠(p,q) × {t}`, so every hole is pure.
- **`t = 1` and `B = {1,x,y}`.** Then `(1,x), (1,y) ∈ 𝔣_s`. Every point of `X₂` extends
  in `M`, so the piece is empty. The leftover `X₂(v; 𝔰 ∪ e)` is empty for the same reason.
- **`B = {1}`.** Then `t = 1`, and every hole is pure, including those of the leftover. ∎

**(St).**
- **(`1_𝔛`)** holds trivially, since units are trivial.
- **(`2_𝔛`).** For an arbitrary `e ⊆ v𝔖₂`,
  `X₂(v;e) = ⊔_{t ∈ {x,y}, (1,t) ∉ e} (1,t)·X₂(v; e_t)`, where
  `e_t = {(q,1) : (q,1) ∈ e or (q,t) ∈ e}` is pure. This is a morphism of `𝐂` from pure
  types.
- **(`1_Γ`)** is Lemma P with `A = 𝔖^♯` and `B = {1,x,y}`.
- **(`2_Γ`).** For `c = (c_𝔠, w)` with `‖c‖ = L`, the set `{s : ‖cs‖ = L}` equals
  `(A × B) ∖ {(1,1)}` with:
  - `A = {p : ‖c_𝔠 p‖ ≤ L}`;
  - `B = {1,x,y}` if `|w| < L`, and `B = {1}` if `|w| = L`.

  So Lemma P applies.

**(LCM).**
- **(`3_Γ`)** holds, since units are trivial.
- **(`4_Γ`).** Take `α ∈ 𝚪` and a non-unit `ω ∈ Π` with `αω ∈ 𝚪`. By (`4_Γ`) for Li's
  maximal datum, `ω ∈ 𝐒`. Its target pieces are domain pieces of `α`, and its domain
  pieces are domain pieces of `αω`. All are pure, so `ω ∈ 𝚪`.
- **(`5_Γ`).** Li's `lem:lcm_bfC` gives `α', β'`, whose factors lie in `𝔖₂^♯` by the
  argument of `lem:maxXG:allCOND`. The new pieces are
  `O_k = c_k^{-1}·(X(a_i; a_i e_i) ∩ X(b_j; b_j f_j) ∩ c_k X)`.
  - Write `a_i = (p,t)`, `c_k = (c,c')` with `t ≼ c'`, and let `(q,1) ∈ e_i`.
  - Then `mcm(c_k, (pq, t)) = mcm_𝔠(c, pq) × {c'}`, and `c_k^{-1}` carries it to the pure
    hole `(c^{-1}m, 1)`. The same holds for the `b_j f_j`.
  - So `O_k` is pure, and `α', β' ∈ 𝚪`.

Hence Li's `cor:lcm` applies and `𝒞` admits lcms. With (St), `cor:ab=gamma` and
`prop:GarsideTFG` give `𝒬(*,*) = Q(𝐂)(*,*) ≅ F((𝒢 × G_2)_Y^Y)`, as in the second part of
Li's `thm:Fn`.

## 3. Doubling and packing

**Doubling moves.** For a pure type `τ = X₂(v;e)`, let `δ_τ = γ(e, {(1,x),(1,y)})`, the
case `A = {1}`, `B = {1,x,y}` of Lemma P.
- Its pieces are `(1,x)·τ` and `(1,y)·τ`, both of type `τ`, and its leftover is empty.
- So `δ_τ ∈ Γ(*)` for every `τ ∈ 𝔛(*)`, with `𝔛(𝐝 δ_τ) = {τ}`.

**Packing.** Setting `ρ_{δ_τ} = 𝐦_𝐔(τ)` satisfies Li's constraint in the definition of
`ρ'`, so `ρ'(𝐔) ≥ Σ_τ 𝐦_𝐔(τ) = |𝐔|`. Units are trivial and there are finitely many
types, so for each `R` only finitely many objects have `|𝐔| < R`. This is (Pack).

## 4. A height from (Acyc)

**Which moves have one piece.** A one-layer pure move with one nonempty piece
`a·X₂(d(a);f)` must have `a = (s,1)`, since a piece under `(s,x)` misses the `y`-branch of
the target. So the move is an identity of subsets `U = s·U'` with `s ∈ 𝔖`, where `U, U'`
are the `𝔠`-parts.

**No cycles.** A cycle `U_0 = s_0·U_1, …, U_{p−1} = s_{p−1}·U_0` of such moves gives
`U_0 = σ·U_0` with `σ = s_0⋯s_{p−1} ∈ 𝔠(v,v)` a non-unit. Hence `U_0 = σ^m·U_0` for every
`m`, so `U_0 ⊆ ∩_m σ^m X(v) ∩ X`. `U_0` is a nonempty open subset of `X`, which contradicts
(Acyc). So the one-piece relation on the finite set `𝔛(*)` is acyclic.

**The height.**
- Let `ℓ(U)` be the length of the longest one-piece chain starting at `U`, with
  `K = max ℓ`, and put `r = K − ℓ`.
- Set `ρ_h(x) = (K+1)·|x| + Σ_i r(U_i)`.
- A one-piece move raises `ρ_h` by `r(U') − r(U) ≥ 1`.
- A move with `k ≥ 2` pieces raises it by at least `(K+1)(k−1) − K ≥ 1`.
- Units preserve `ρ_h`. So `ρ_h` is a height with values in `ℤ_{≥0}`.
- It has finite sublevels, since `ρ_h ≥ |x|` and there are finitely many objects of each
  size.

## 5. Conclusion

Item 3 of `perron-weights-do-not-give-li-finiteness` (with §4 of its proof) runs Witzel's
`thm:Wit` with `ρ_h`.
- Li's `lem:link:n-conn_1`, `_2` and `_3` and `cor:link:n-conn` are used as stated.
- Lemma 3's hypothesis `ρ'(x) ≥ R` holds whenever `ρ_h(x) ≥ (2K+1)R`: then `|x| ≥ R`,
  and `ρ'(x) ≥ |x|` by §3.
- `lem:Stab` holds with trivial unit groups, which are `F_∞`.

So `𝒬(*,*) ≅ F((𝒢 × G_2)_Y^Y)` is of type `F_n` for every `n`. ∎

## 6. Where each hypothesis is used

- **Trivial units:** objects up to units are multisets of types (§3), and `lem:Stab` is
  trivial.
- **(Acyc):** only the height (§4). Without it, a one-piece cycle is a non-unit
  endomorphism of an object of `𝒞`, and no height exists. Example: `ℕ × M`.
- **Pure holes:** they keep every type doublable (§3). With Li's maximal datum, the
  partial split `X₂(v;∅) → ((1,x)·X₂(v;∅), X₂(v;{(1,x)}))` produces a copy of `𝔠`'s
  thin cycles among the types with a Cuntz hole. For raw tree codings (Pack) then fails,
  by `thin-cycles-decide-li-packing`.

## 7. Checking (Acyc)

- **1-graphs.** `∩ σ^m X(v)` is the single path `σ^∞`, so (Acyc) says exactly that `X`
  has no isolated points.
- **Products of thick trees with `X = ∏ ∂T_i`.** A loop `σ` projects to a ray or a point
  in each factor. So `∩ σ^m X(v)` is a product of single ends and cones, with at least
  one single-end factor, and it has empty interior.
- **Pointed-cube categories in general.** Here (Acyc) says that no nonempty open subset
  of `X` lies beyond the axis ray of a single element. This is gate (G2) for Q1.15.

## 8. Reading note on Li's `lem:link:n-conn_3`

Li defines `ρ'` with `ρ_γ` for all `γ ∈ Γ`. Read literally, the lemma is false. Take the
cone datum on the raw `F_2` coding (`perron-weights-do-not-give-li-finiteness-proof`) and
add to `𝔛` the type `X(a; {a→a})`, together with its forced expansion to `(b, b^{-1})`.
- That type never occurs in `𝐗(*)`, so `𝒞`, `E(x_N)` and `M_{x_N}` do not change.
- (St) and the lcms still hold.
- But now `ρ'(x_N) ≥ N`.
- The 1-simplex `{A(1,1), B(2,2)}` of `M_{x_N}` has no extension, for every `N`.

So `ρ'` must range over `Γ(*)`, and it does in all our uses. Li's own theorems are
unaffected: his (`t<d`) quantifies over `Γ(*)`.

## Lesson for general BH

The Cuntz colour is a universal packing device. It makes every cylinder mergeable with a
copy of itself, so only order-theoretic hypotheses remain: a height and Li's lattice
hypotheses. The one thing to avoid is letting the datum contain cylinders the Cuntz move
cannot double.
