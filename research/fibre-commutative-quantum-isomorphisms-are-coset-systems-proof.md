---
rg: 2
id: fibre-commutative-quantum-isomorphisms-are-coset-systems-proof
kind: route
title: Commuting fibre blocks decompose into minimal projections indexed by fibre isomorphisms, and the cross colours cut out cosets of the colour stabilizers
target: fibre-commutative-quantum-isomorphisms-are-coset-systems
requires: []
---

Notation as in the target.  All statements are identities in `A^fc(X,Y)`.

**(Q1) Fibre blocks are magic unitaries.**
- If `c_X(x,x) != c_Y(a,a)`, then `v_(xa) = v_(xa)^2 = 0`.  So `v_(xa) = 0`
  across fibres, and rows and columns of each fibre block sum to `1`.
- The in-fibre relations are those of `A(Iso(W_q^X, W_q^Y))`.  So the fibre
  block is a representation of that algebra.

**(Q2) Minimal projections of a commuting fibre block.**
- **Definition.**  For a bijection `φ : F_q^X -> F_q^Y` put
  `p_q^φ = prod_(x in F_q^X) v_(x, φ(x))`.  The factors commute.
- **Colours.**  If `φ` fails to preserve colours at `(x,x')`, then
  `v_(x,φx) v_(x',φx') = 0` by (Q1), so `p_q^φ = 0`.
- **Partition of unity.**
  - Expand `1 = prod_x sum_a v_(xa)` over all functions `f : F_q^X -> F_q^Y`.
  - A non-injective `f` has `f(x) = f(x') = a` with `x != x'`, and the product
    contains `v_(xa) v_(x'a) = 0`, since columns are PVMs.
  - So `sum_(φ in Iso(W_q^X, W_q^Y)) p_q^φ = 1`.
- **Orthogonality.**  `p_q^φ p_q^ψ = 0` for `φ != ψ`, since some
  `v_(x,φx) v_(x,ψx) = 0`.
- **Reconstruction.**  `v_(xa) = v_(xa) prod_(x' != x) sum_(a') v_(x'a')`
  gives `v_(xa) = sum_(φ(x) = a) p_q^φ`.
- **Degenerate case.**  If `Iso(W_q^X, W_q^Y)` is empty, then `1 = 0`.

**(Q3) Cross relations.**  Fix `q != q'`, `φ in Iso_q` and `ψ in Iso_(q')`.
- **Necessity.**  By (Q2), `p_q^φ v_(xa) = [φx = a] p_q^φ` and
  `v_(x'a') p_(q')^ψ = [ψx' = a'] p_(q')^ψ`.  So
  `p_q^φ (v_(x,φx) v_(x',ψx')) p_(q')^ψ = p_q^φ p_(q')^ψ`.
  - If `c_Y(φx, ψx') != c_X(x,x')` for some `x, x'`, the middle product is `0`.
  - So `p_q^φ p_(q')^ψ = 0` unless `(φ,ψ)` preserves the cross colours.
- **Sufficiency.**  Conversely, suppose these products vanish.  Then
  `v_(xa) v_(x'a') = sum_(φx = a, ψx' = a') p_q^φ p_(q')^ψ`, and every surviving
  term has `c_Y(a,a') = c_X(x,x')`.  So the iso relations follow.
- **Transport to `K_q`.**  With `φ = φ_q k` and `ψ = φ_(q') l`, the surviving
  pairs are exactly `R_(qq')`.

**(Q4) `R_(qq')` is a coset.**
- Suppose `(k_0,l_0) in R` and put `k = k_0 k'`, `l = l_0 l'`.
- Applying the defining identity of `(k_0,l_0)` at the points `k'x, l'x'`
  gives `c_Y(φ_q k x, φ_(q') l x') = c_X(k'x, l'x')`.
- So `(k,l) in R` iff `c_X(k'x, l'x') = c_X(x,x')` for all `x, x'`, i.e.
  `(k',l') in D_(qq')`.
- Hence `R = (k_0,l_0) D_(qq')`.  `D` is a subgroup, the stabilizer of the
  cross colouring, and the transpose data give `R_(q'q)`.
- If `R` is empty, then `1 = sum_(k,l) p_q^k p_(q')^l = 0`.

**(Q5) The isomorphism `A(S) ≅ A^fc(X,Y)`.**
- **`A(S) -> A^fc`.**  Send `p_q^k |-> p_q^(φ_q k)`.  These are PVMs by (Q2),
  and the relations (CS) hold by (Q3).
- **`A^fc -> A(S)`.**  Send `v_(xa) |-> sum_(k : φ_q k x = a) p_q^k` for `x, a`
  in the fibre of `q`, and `0` across fibres.
  - **Rows and columns.**  Each `φ_q k` is a bijection, so row and column sums
    are `sum_k p_q^k = 1`.
  - **In-fibre relations.**  Every term of `v_(xa) v_(x'a')` has
    `φ_q k in Iso(W_q^X, W_q^Y)`, so a colour mismatch leaves an empty sum.
  - **Fibre commutativity.**  All entries lie in `C*(p_q)`.
  - **Cross relations.**  They follow from (CS) as in (Q3).
- **Inverse on generators.**
  - `p_q^k |-> prod_x v_(x, φ_q k x) |-> prod_x sum_(k' x = k x) p_q^(k')`.
    This equals `p_q^k`, because `K_q` acts faithfully.
  - `v_(xa)` returns to `sum_(φ(x) = a) p_q^φ = v_(xa)` by (Q2).

**(Q6) Rigid fibres (F3).**
- If `A(Iso(W_q^X, W_q^Y))` is commutative, the fibre block entries commute in
  `A(Iso(X,Y))` by (Q1).  So the commutator ideal is zero and
  `A(Iso(X,Y)) = A^fc(X,Y)`.
- If `φ_q` exists, relabeling `a |-> φ_q^(-1) a` identifies
  `A(Iso(W_q^X, W_q^Y))` with `O(Qut W_q^X) = A(Iso(W_q^X, W_q^X))`.
- Traciality and `R^U` models transfer along the isomorphism.

**(Q7) Trace level (F4).**  `pi_tau` kills every fibre commutator, so it
factors through `A^fc(X,Y) ≅ A(S)`.

**(Q8) Ports (F5).**  By (Q5),
`v_(x_q, a) = sum_(k : φ_q k x_q = a) p_q^k = sum_(beta_q(k) = a) p_q^k`.
Relation sets of `S` map into the accepted pairs of the completion.

**(Q9) Model tests.**
- **Cayley fibres.**
  - If `σ` preserves the colours `x^(-1)x'`, then
    `σ(x)^(-1) σ(x') = x^(-1) x'`, so `σ(x) = σ(e) x`.  Hence
    `K_q = K_q` by left translation.
  - Rows commute because `v_(xa) v_(x'a') = 0` unless `a' = a x^(-1) x'`.
    As in (R3) of `coset-refinement-forces-rectangular-central-splitting-proof`,
    this forces `v_(xa) = v_(e, a x^(-1))`, and a single PVM row commutes.
  - Take `X = X(S_1)`, `Y = X(S)` and `φ_q = id`.  On an edge, `(k,l)` is in
    `R` iff `D c^(-1) (kx, lx') = D (x,x')` for all `x, x'`.  That holds iff
    `D c^(-1) (k,l) = D`, i.e. `(k,l) in cD`.
  - On a free pair the colour is constant, so `R = K_q x K_(q')`.
- **`S_3`.**
  - A permutation `g` and a pair `(g, h)` preserve incidence iff `h` is `g`
    acting on 2-subsets.  So `D` is diagonal.
  - `p^g p'^h = 0` for `h != g` forces `p = p'`, and `A = C(S_3) = C^6`.
- **`K_4`.**  Wang's `S_4^+` is noncommutative, and the abelianization of
  `O(S_4^+)` is `C(S_4)`.
