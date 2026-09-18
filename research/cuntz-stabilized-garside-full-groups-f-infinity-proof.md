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
  - cuntz-pure-hole-datum-satisfies-li-st-and-lcm
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

*(Revised 2026-09-18 to integrate referee bh-ref-q115-a, 9580d05636.)* We run Witzel's
`thm:Wit` with the height `ρ_h` of §4, following Li's proof of `thm:Fn` with these inputs:
- **`lem:link:n-conn_1`** (down-links), used as stated. It uses only gcds in `Div(Δ)`,
  which exist since `𝒞` has lcms (§2).
- **Lemma L, in place of `lem:link:n-conn_3`.** Fix `n, L, m`. There is `R` such that for
  every `x ∈ 𝐗(*)` with `|x| ≥ R`, every `[μ] ∈ E(x)` with fewer than `n+1` components in
  `μ_+ ⊔ μ_a`, and all `m`-simplices `σ_1, …, σ_L` of `𝓜_μ`, some vertex `[α]` makes every
  `σ_l ∪ {[α]}` a simplex.

  *Proof* (bh-ref-q115-a). Let `𝐑` be the set of multisets of objects of `𝐗(*)`.
  - Membership in `𝐗(*)` depends only on the multiset, since units are trivial.
  - `𝐑` is closed under `𝐦 ↦ 𝐦 + e_τ` whenever `𝐦(τ) ≥ 1`, by applying `δ_τ` (§3).
  - By Dickson's lemma, each support class of `𝐑` has finitely many minimal elements.
    Let `C` be 2 plus their largest coordinate. Then `𝐦 ∈ 𝐑` and `𝐦(τ) ≥ C` imply
    `𝐦 − e_τ ∈ 𝐑`.
  - The simplices and `μ_+ ⊔ μ_a` touch at most `(n + Lm)B` pieces. Take
    `R = (n+Lm)B + |𝔛(*)|(C+2)`. Then some type `τ` has at least `C+2` untouched pieces.
  - Let `α` be the doubling atom `δ_τ` on two untouched `τ`-pieces. It is an atom of `𝒮`:
    its only coarsening with pure pieces is the whole piece.
  - Each `O_l = 𝐭(ν_l)` has `𝐦_{O_l}(τ) ≥ C+2`. Applying `α` gives multiset
    `𝐦_{O_l} − e_τ ∈ 𝐑`, which is an object of `𝐗(*)`. So every `σ_l ∪ {[α]}` is a
    simplex. ∎

  The full text is in the Referee A section below.
- **`lem:link:n-conn_2`** follows from Lemma L by Li's deduction (Matui, Lemma 6.18;
  Brown, Lemma 4.20). Its hypothesis only concerns the `y`-part of `x`, and the argument
  above already takes that into account.
- **`cor:link:n-conn`**, with `ρ_h` in the Morse function. §4 gives `|x| ≥ R` whenever
  `ρ_h(x) ≥ (2K+1)R`.
- **`lem:Stab`** holds with trivial unit groups, which are `F_∞`.

The packing number `ρ'` and item 3 of `perron-weights-do-not-give-li-finiteness` are no
longer used.

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

So the literal reading fails, and `ρ'` would have to range over `Γ(*)`.

**What Li's written proof supplies (neutral record, following bh-ref-q115-a).** Li's framework
for finiteness of full groups is the basis of this whole route:
- the bisection category;
- Garside maps;
- the complexes `E(x)` and `𝓜_μ`;
- the use of Witzel's criterion.

Two points of the written text matter here.
- **The proof of `lem:link:n-conn_3`** (arXiv:2110.04505v2, l.1733–1759) uses `ρ'` only to
  choose a sequence with `ρ'(x_p) → ∞`. Its key step asserts, without further argument, an
  element `θ ∈ 𝒞` with `𝐝(θ) ⊆ z_{p+2,l}` and a prescribed multiplicity change.
- **Nothing in it distinguishes `Γ` from `Γ(*)`.** So the example above shows that the step
  needs an argument that the text does not give.

We have not checked whether the step can be supplied under Li's (`t<d`), so nothing here is
claimed about Li's theorems. What this route supplies instead is Lemma L (§5), a direct
proof of the instance needed for pure-hole Cuntz data, by Dickson's lemma and doubling.

## Lesson for general BH

The Cuntz colour is a universal packing device. It makes every cylinder mergeable with a
copy of itself, so only order-theoretic hypotheses remain: a height and Li's lattice
hypotheses. The one thing to avoid is letting the datum contain cylinders the Cuntz move
cannot double.

## Referee A (bh-ref-q115-a, 2026-09-18): the Γ(*) reading of §8 is not supplied by Li; a direct proof for pure-hole data

**The gap.** Li's proof of `lem:link:n-conn_3` (arXiv:2110.04505v2, l.1733–1759, read at
source) uses `ρ'` only to choose a sequence with `ρ'(x_p) → ∞`. The key step, "there exists
`θ ∈ C`, independent of `l`, with `𝐝(θ) ⊆ z_{p+2,l}` and `𝐦_θ = 𝐦_{ξ_{p+1,l}} − 𝐦_{ξ_{p,l}}`",
is asserted without argument, and nothing in the proof distinguishes `Γ` from `Γ(*)`. So if §8's
counterexample to the literal reading is right (I find it convincing), Li's written proof has a
gap at that step, and the `Γ(*)` reading is not proved by Li's text either. The weakest link is a
missing proof, not a reading question.

**Repair for this node's setting** (pure-hole datum on `𝔠 × M`, trivial units). Replace the
hypothesis `ρ'(x) ≥ R` by `|x| ≥ R` (piece count). §5 gives `|x| ≥ R` whenever
`ρ_h(x) ≥ (2K+1)R`. Let `𝐑 = {𝐦_x : x ∈ 𝐗(*)}`.
1. **Membership is a multiset property.** Objects with equal multisets are unit-isomorphic; Li
   uses this himself at l.1758.
2. **Doubling closure.** If `𝐦 ∈ 𝐑` and `𝐦(τ) ≥ 1`, then `𝐦 + e_τ ∈ 𝐑`. Expanding one
   `τ`-piece by `δ_τ ∈ Γ(*)` gives `x'` with a morphism `x' → x → *`.
3. **Eventual downward closure (Dickson).**
   - For each support `S ⊆ 𝔛(*)`, the set `𝐑_S = 𝐑 ∩ {supp = S}` is upward closed inside
     support `S`, by 2.
   - So `𝐑_S` is the union of the cones above its finitely many minimal elements.
   - Let `C` be 2 plus the largest coordinate of any minimal element, over all `S`.
   - If `𝐦 ∈ 𝐑` and `𝐦(τ) ≥ C`, then `𝐦 − e_τ ∈ 𝐑`: it dominates the same minimal element and
     keeps support `S`.
4. **The extension.**
   - Let `B` bound the number of domain pieces of any element of `𝓛` and of any atom of `𝒮`.
     This is finite: `𝔖₂` is locally finite and there are finitely many types.
   - Take `[μ]` with fewer than `n+1` components in `μ_+ ∐ μ_a`, and `m`-simplices
     `σ_1, …, σ_L` of `𝓜_μ`. They touch at most `(n + Lm)B` pieces of `x`.
   - If `|x| ≥ R := (n+Lm)B + |𝔛(*)|·(C+2)`, some pure type `τ` has at least `C+2` untouched
     pieces in `y`.
   - Let `α` be the first atom factor of `δ_τ`, acting on two untouched `τ`-pieces. It lies in
     `𝒮 = Div(Δ)`, since `δ_τ` does.
   - For each `l`, the object `O_l = 𝐭(ν_l) ∈ 𝐗(*)` contains every untouched piece. So
     `𝐦_{O_l}(τ) ≥ C+2`, and `𝐦_{O_l} − e_τ ∈ 𝐑` by 3.
   - Applying `α` to `O_l` gives an object with a morphism to that `(𝐦_{O_l} − e_τ)`-object,
     so it lies in `𝐗(*)`. Hence `σ_l ∪ {[α]}` is an `(m+1)`-simplex for every `l`.

So the instance of `lem:link:n-conn_3` that §5 uses holds, with `R = R(n,L,m)`, and Li's deduction
of `lem:link:n-conn_2` (via Matui Lemma 6.18 and Brown Lemma 4.20) goes through as stated. The rest
of §5 is unchanged, and this fix needs no packing number at all.

Not re-checked here: §2, i.e. that the pure-hole datum satisfies (St) and has lcms.
