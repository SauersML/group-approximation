# The Brin–Thompson group 2V as a Gottschalk host

Lane `w6-free-neg-d`, 2026-09-12. Artifact for `brin-thompson-2v-nonsurjunctive`.

## 0. Why this host

- **Untested.** The roots under the goal's `refuted_by` are the Leavitt unit groups (binary, ternary, projective
  ternary, finite field), a lattice in a product of trees, the Kun–Thom Clifford covers and wreath lamp
  quotients, Deligne's triple cover and Higman's group. `thompson-v-nonsurjunctive` is the root for `V`. On main
  (tip `c0ffe2f06`), Brin–Thompson groups appear only as twisted Brin–Thompson envelopes in the Boone–Higman
  region. No node uses one as a Gottschalk host.
- **Weaker than V.** `2V` contains `V` (Section 1). So `thompson-v-nonsurjunctive` ascends to `2V`, and every
  complement-corner statement for `V` implies the one for `2V` (Corollary 2.2).
- **New feature.** The halving endomorphism `D` of Theorem B maps `V` into a proper subgroup of itself. Inside
  `2V` it becomes conjugation by one group element, the baker unit (Lemma 2.3). No element of `V` does this.

## 1. Setup

- `R = L_(F_2)(1,2)` with `s0, s1, t0, t1`. For a word `α = a_1 ... a_n` put `s_α = s_(a_1) ... s_(a_n)`,
  `t_α = t_(a_n) ... t_(a_1)`, `p_α = s_α t_α`, and `[α]` for its cylinder in the binary Cantor set `C`.
  Then `t_α s_β` is `s_(β')` if `β = αβ'`, `t_(α')` if `α = βα'`, and `0` if `α`, `β` are incomparable.
- `B = R ⊗_(F_2) R`. It acts on the `F_2`-space with basis `δ_(x,y)`, `(x, y)` in `C × C`, by
  `(s_a ⊗ 1) δ_(x,y) = δ_(ax,y)`, `(t_a ⊗ 1) δ_(bx,y) = [a = b] δ_(x,y)`, and likewise in the second coordinate.
- **Product monomial units.** `u = Σ_k s_(α_k) t_(β_k) ⊗ s_(γ_k) t_(δ_k)`, where `{[α_k] × [γ_k]}` and
  `{[β_k] × [δ_k]}` are partitions of `C × C` into product cylinders, with one index set.
  - `u` permutes the basis: `δ_(β_k x, δ_k y) -> δ_(α_k x, γ_k y)`.
  - `u^(-1) = Σ_k s_(β_k) t_(α_k) ⊗ s_(δ_k) t_(γ_k)`. In `u u^(-1)`, a cross term `k != l` contains
    `t_(β_k) s_(β_l) ⊗ t_(δ_k) s_(δ_l)`. The cylinders `[β_k] × [δ_k]` and `[β_l] × [δ_l]` are disjoint, so one
    of the two word pairs is incomparable and the term vanishes. The diagonal is `Σ_k p_(α_k) ⊗ p_(γ_k) = 1`:
    `p_α = p_(α0) + p_(α1)` refines any partition to a grid of words of fixed lengths, where the sum is `1 ⊗ 1`.
  - Products of such units are such units (refine the middle partitions until they agree).
  - Two expressions with the same point map are equal in `B`. Refine both to a common domain partition. On a
    product cylinder, `(βx, δy) -> (αx, γy)` determines `α` and `γ`, because `αx = α'x` for all `x` forces
    `α = α'`.
  - So these units form a group isomorphic to the group of homeomorphisms of `C × C` that are piecewise product
    prefix replacements. That group is the Brin–Thompson group `2V`, and this note works in the unit model.
    Nothing below uses a presentation of `2V`, its simplicity or its finite presentability.
- **The copies of V.** `V` is the group of monomial units `Σ_k s_(α_k) t_(β_k)` of `R` (complete prefix codes).
  `x -> x ⊗ 1` and `x -> 1 ⊗ x` are injective unital algebra maps `R -> B`. Put `V_1 = V ⊗ 1` and `V_2 = 1 ⊗ V`.
  Both are subgroups of `2V`, and they commute.
- **Ternary family.** `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1` (words `w_1 = 0`, `w_2 = 10`, `w_3 = 11`), with
  `t_i` dual, in either coordinate. `g = s_2 t_1 + s_3 t_2 + s_1 t_3` lies in `V`, and so do the nine-cylinder
  permutation units `π_M` of Section 0 of `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md`,
  cited below as [CS].
- **Halving.** `D(X) = Σ_(i=1..3) (s_i ⊗ 1) X (t_i ⊗ 1)` is a unital algebra endomorphism of `B`.
  - It is injective: `(t_1 ⊗ 1) D(X) (s_1 ⊗ 1) = X`.
  - `D(s_α t_β ⊗ Y) = Σ_i s_(w_i α) t_(w_i β) ⊗ Y`. So `D(2V) ⊆ 2V` and `D(V_1) ⊆ V_1`.
  - On `V_1 ≅ V` it is the `D` of the binary Theorem B.
  - Write `D_2(Y) = Σ_i s_i Y t_i` for the same map on `R`, used in the second coordinate.

## 2. Transfer, baker unit, product tower

Throughout, `A = F_2[2V]`, `e^(1) = 1 + [g ⊗ 1] + [g² ⊗ 1]`, `e^(2) = 1 + [1 ⊗ g] + [1 ⊗ g²]`,
`f^(i) = 1 - e^(i)`, and `T = f^(1) A f^(1)`.

**Proposition 2.1 (Theorem B transfers).** Theorem B of `binary-cyclic-corner-full-iff-complement-corner-has-no-state`
holds for `A = F_2[2V]`, with `e = e^(1)` and `f = f^(1)`. In particular `c e b = 1` is solvable in `A` iff
`(K_0(T), [T])` has no state. When it is solvable, `A` is not directly finite and `2V` is not surjunctive.

*Proof.*
- **Theorem B applies.** The node's Scope paragraph and [CS] Section 2 cover subgroups of the units of `R`. `2V`
  lies in the units of `B`, so it is not such a subgroup. The proof of [CS] Theorem B (Sections 0–2) uses only
  three inputs, and each holds for `H = 2V`.
  - The identities among `g`, the `D^j(g)` and the `π_M` hold in `V`, and `x -> x ⊗ 1` carries them into `2V`,
    since `D(X ⊗ 1) = D_2(X) ⊗ 1`.
  - `D` is an injective endomorphism of `2V` (Section 1).
  - `D(h)` commutes with every ternary permutation unit `π ⊗ 1`, `g ⊗ 1` included, since
    `(π ⊗ 1) D(h) (π ⊗ 1)^(-1) = Σ_i (s_(τ(i)) ⊗ 1) h (t_(τ(i)) ⊗ 1) = D(h)`.
- **Directly finite fails.** From `c e b = 1`, put `d = c` and `a = e b`, so `d a = 1`. If `a d = 1`, then
  `e (b c) = 1`, hence `e = e · e b c = e b c = 1`. That is false, because `g ⊗ 1 != 1`.
- **Not surjunctive.** Apply `stable-finiteness-failure-refutes-surjunctivity`. QED

**Corollary 2.2 (2V's condition is weaker than V's).** Suppose `(K_0(f F_2[V] f), [f])` has no state, with
`f = 1 - e` in `F_2[V]`. Then `(K_0(T), [T])` has no state either. The converse is not claimed.

*Proof.* `x -> x ⊗ 1` gives a unital ring map `f F_2[V] f -> T`. A state on `K_0(T)` pulls back along `K_0` of
this map to a state on `K_0(f F_2[V] f)`. QED

**Lemma 2.3 (baker unit).** Let `u = Σ_(i=1..3) s_i ⊗ t_i`.
- (a) `u` is a product monomial unit (terms `s_(w_i) t_∅ ⊗ s_∅ t_(w_i)`, partitions `{[w_i] × C}` and `{C × [w_i]}`).
  Its point map is the ternary baker's map `(x, w_i y) -> (w_i x, y)`, and `u^(-1) = Σ_i t_i ⊗ s_i`.
- (b) `u (X ⊗ 1) u^(-1) = D(X ⊗ 1) = D_2(X) ⊗ 1` for every `X` in `R`.
- (c) `u^(-1) (1 ⊗ Y) u = 1 ⊗ D_2(Y)` for every `Y` in `R`.
- (d) `u (1 ⊗ π) u^(-1) = π ⊗ 1` for every ternary permutation unit `π = Σ_k s_(τ(k)) t_k`, `τ` in `Sym(3)`.
  In particular `u^(-1) (g ⊗ 1) u = 1 ⊗ g`.
- (e) No element of `V` conjugates `V` into `D_2(V)`.

*Proof.*
- (a) `u u^(-1) = Σ_(i,j) s_i t_j ⊗ t_i s_j = Σ_i s_i t_i ⊗ 1 = 1`, and `u^(-1) u = Σ_(i,j) t_j s_i ⊗ s_j t_i = 1`.
- (b) `u (X ⊗ 1) u^(-1) = Σ_(i,j) s_i X t_j ⊗ t_i s_j = Σ_i s_i X t_i ⊗ 1`.
- (c) `u^(-1) (1 ⊗ Y) u = Σ_(i,j) t_i s_j ⊗ s_i Y t_j = Σ_i 1 ⊗ s_i Y t_i`.
- (d) `u (1 ⊗ π) u^(-1) = Σ_(i,j) s_i t_j ⊗ t_i π s_j`, and `t_i π s_j = [i = τ(j)]`.
- (e) Suppose `h V h^(-1) ⊆ D_2(V)` for some `h` in `V`. Then `V ⊆ D_2(V)`, and `D_2(V)` commutes with `g`
  (the Theorem B remark on `D(h)` and `π`). But the ternary transposition unit `π = s_2 t_1 + s_1 t_2 + s_3 t_3`
  gives `π g π^(-1) = g² != g`. QED

**Proposition 2.4 (the halving tower is a product tower).** Let `E_k` be the averaging idempotent of
`C_3^k ⊗ 1 = ⟨g, D_2(g), ..., D_2^(k-1)(g)⟩ ⊗ 1` (`E_0 = 1`, `E_1 = e^(1)`), and `E_k^(2)` the same in `V_2`.
Let `ψ(X) = e^(1) D(X)` be the halving homomorphism of [CS] Lemma 1.1. In `A`:
- (a) `u^(-1) ψ(X) u = e^(2) X` for every `X` in `F_2[V_1]`;
- (b) `u^(-j) E_k u^j = E_(k-j) E_j^(2)` for `0 <= j <= k`, a commuting product; in particular `u^(-k) E_k u^k = E_k^(2)`;
- (c) in `K_0(A)`, `[ψ(P)] = [e^(2) P]` for every idempotent matrix `P` over `F_2[V_1]`, and
  `[E_k] = [E_(k-j) E_j^(2)]` for `0 <= j <= k`.

*Proof.*
- (a) By Lemma 2.3(b), `D(X) = u X u^(-1)` on `F_2[V_1]`, so `u^(-1) ψ(X) u = (u^(-1) e^(1) u) X`. By 2.3(d),
  `u^(-1) e^(1) u = e^(2)`.
- (b) By 2.3(b), `u^(-1) (D_2^j(g) ⊗ 1) u = D_2^(j-1)(g) ⊗ 1` for `j >= 1`. By 2.3(d) the case `j = 0` gives
  `1 ⊗ g`, and by 2.3(c) `u^(-1) (1 ⊗ D_2^j(g)) u = 1 ⊗ D_2^(j+1)(g)`. Conjugation by a group element maps the
  averaging idempotent of a finite subgroup to that of its conjugate. `C_3^(k-j) ⊗ 1` and `1 ⊗ C_3^j` commute and
  meet trivially, so the averaging idempotent of their product is the product. Induct on `j`.
- (c) Conjugate idempotents have isomorphic right ideals and equal rank. QED

**Proposition 2.5 (torsion relations are consistent).** For a state `s` of `(K_0(A), [A])`, put
`a = s[e^(1) e^(2)]`, `b = s[e^(1) f^(2)]`, `c = s[f^(1) e^(2)]` and `d = s[f^(1) f^(2)]`. Then `b = c`, `d = 2b` and
`a + 4b = 1`.

*Proof.*
- The four idempotents are orthogonal with sum `1`, so `a + b + c + d = 1`.
- `e^(2)` is conjugate to `e^(1)` (Lemma 2.3(d)), so `a + b = a + c`.
- [CS] Lemma 1.2(b) gives `[f^(1)] = 3[E_1 - E_2]`. It holds in `F_2[V_1]` by the Theorem B scope remark, and
  so in `A`. Conjugating by `u^(-1)` turns `E_1 - E_2` into
  `e^(2) - e^(1) e^(2) = f^(1) e^(2)`, so `c + d = 3c`. QED

The relations allow every `b` in `[0, 1/4]`:
- `b = 0` is the augmentation;
- `b = 2/9` is the independent product of the two regular values `s[e^(i)] = 1/3`.

So the baker unit forces no contradiction through the finite subgroups alone. An obstruction to states on `T`,
or a state, has to involve elements of infinite order that mix the two coordinates.

## 3. Where this stands (first landing)

- **Payoff chain.** Suppose `(K_0(T), [T])` has no state. Proposition 2.1 then gives `c e b = 1` in `F_2[2V]`
  (`brin-thompson-2v-order-three-averaging-idempotent-is-full`), so by
  `brin-thompson-2v-nonsurjunctive-from-averaging-fullness`
  `F_2[2V]` is not directly finite and `2V` is not surjunctive. Gottschalk's conjecture fails, and `2V` is not
  sofic.
- **Inputs from V.** The complement-corner condition for `V` gives the one for `2V` (Corollary 2.2). A strict
  automaton over `V` gives one over `2V` (route `thompson-v-nonsurjunctivity-ascends-to-brin-thompson-2v`).
  Fullness over `V` gives fullness over `2V` (route `brin-thompson-2v-averaging-fullness-ascends-from-v`).
- **Where it stops.** Proposition 2.5: the baker unit turns halving into an external product, and the torsion
  relations it imposes are consistent with independent product states. The next handle has to use infinite-order
  elements of `2V` that no product `V_1 × V_2` contains. Section 4 shows that `V_1` together with the baker unit
  is not enough.

## 4. The baker subgroup is an ascending HNN extension of V

Put `H_u = ⟨V_1, u⟩ <= 2V`, and let `σ` be the ternary shift on `C`, `σ(w_i y) = y`. The code `{0, 10, 11}` is
complete and prefix, so every `y` in `C` factors uniquely as an infinite word in the letters `w_i`. Call `y`
aperiodic when that letter sequence is not eventually periodic.

**Lemma 4.1 (ternary index).** Let `H` be the set of `h` in `2V` for which some integer `k` has the following
property. For every `(x, y)`, writing `h(x, y) = (x', y')`, there are `p, q >= 0` with `p - q = k` and
`σ^p(y) = σ^q(y')`. Then `k = ι(h)` is unique, `H` is a subgroup, and `ι : H -> Z` is a homomorphism with
`ι(V_1) = 0` and `ι(u) = 1`. So `H_u <= H`.

*Proof.*
- **Uniqueness.** Suppose `σ^p(y) = σ^q(y')` and `σ^(p')(y) = σ^(q')(y')`, with `p' >= p`. Then
  `σ^(q')(y') = σ^(q + p' - p)(y')`. If `q' != q + p' - p`, the letter sequence of `y'` is eventually periodic,
  and so is that of `y`. At an aperiodic `y`, the difference `p - q` is therefore determined.
- **Products.** Take `σ^p(y) = σ^q(y')` for `h` at `(x, y)`, and `σ^(p')(y') = σ^(q')(y'')` for `h'` at
  `h(x, y)`. Then `σ^(p + p')(y) = σ^(q + p')(y') = σ^(q + q')(y'')`. So `h' h` lies in `H`, with index
  `ι(h) + ι(h')`.
- **Inverses.** Read the defining equation at the point `h(x, y)`: `h^(-1)` has index `-ι(h)`.
- **Generators.** `V_1` fixes the second coordinate (`p = q = 0`). `u(x, w_i y) = (w_i x, y)` (`p = 1`, `q = 0`). QED

**Proposition 4.2.** The assignment `x -> x ⊗ 1` (`x` in `V`), `τ -> u` is an isomorphism from the ascending HNN
extension `V *_(D_2) = ⟨V, τ | τ x τ^(-1) = D_2(x) for x in V⟩` onto `H_u`.

*Proof.*
- **Well defined.** Lemma 2.3(b).
- **Normal form.** Every element of `V *_(D_2)` has the form `τ^(-n) x τ^m`, with `x` in `V` and `n, m >= 0`. The set
  of such elements contains `V` and `τ^(±1)` and is closed under inverses. It is closed under products by
  `τ x = D_2(x) τ` and `x τ^(-1) = τ^(-1) D_2(x)`.
- **Injective.** If `u^(-n) (x ⊗ 1) u^m = 1`, then `ι` gives `m = n`, so `x ⊗ 1 = 1` and `x = 1`.
- **Onto.** `H_u` is generated by the images. QED

**Corollary 4.3.** `H_u` is sofic iff `V` is sofic.

*Proof.*
- `V ≅ V_1 <= H_u`, and subgroups of sofic groups are sofic.
- Conversely, put `N = ∪_(n >= 0) u^(-n) V_1 u^n`. The union is increasing, because
  `x ⊗ 1 = u^(-1) (D_2(x) ⊗ 1) u`. So `u^(-1) N u ⊆ N`, and `u N u^(-1) ⊆ N` because
  `u V_1 u^(-1) = D_2(V) ⊗ 1 ⊆ V_1`. So `N` is normal in `H_u`. `H_u / N` is generated by the image of `u`, so it is
  cyclic (`ι` makes it `Z`).
- Every finitely generated subgroup of `N` lies in some `u^(-n) V_1 u^n ≅ V`. So `N` is sofic when `V` is, because
  soficity is decided on finitely generated subgroups. `sofic-kernel-amenable-quotient-permanence` then makes
  `H_u` sofic. This is the sofic counterpart of `ascending-hnn-cannot-create-nonhyperlinearity`. QED

**Corollary 4.4 (the Section 2 lever stays at V's level).**
- Every idempotent in Propositions 2.4–2.5 lies in `F_2[H_u]`, because `1 ⊗ D_2^j(g) = u^(-j-1) (g ⊗ 1) u^(j+1)`
  (Lemma 2.3(c)–(d)).
- Suppose `c e b = 1` has a solution with `b, c` in `F_2[H_u]`. Then `F_2[H_u]` is not directly finite, by the
  argument of Proposition 2.1. So `H_u` is not surjunctive (`stable-finiteness-failure-refutes-surjunctivity`),
  hence not sofic (`sofic-groups-are-surjunctive`), and `V` is not sofic by Corollary 4.3.
- So a fullness proof built only from `V_1` and the baker unit would decide `thompson-v-not-sofic`. QED

**Remark 4.5 (what lies outside).**
- `1 ⊗ h` is not in `H`, where `h = (00, 01, 1) -> (01, 1, 00)` is the element of
  `thompson-v-order-three-averaging-idempotent-is-full`. Take `y''` aperiodic.
  - `(x, 000y'') -> (x, 010y'')` has index `1`: letters `w_1 w_1 w_1 y''` become `w_1 w_2 y''`.
  - `(x, 0010y'') -> (x, 0110y'')` has index `0`: letters `w_1 w_1 w_2 y''` become `w_1 w_3 w_1 y''`.
  - So `V_2` is not contained in `H_u`.
- By Lemma 2.3(c), `⟨V_2, u⟩` is the ascending HNN extension of `V_2` along `D_2`, with stable letter `u^(-1)`. The
  ternary index of the first coordinate plays the role of `ι`, and Corollary 4.3 holds for it.
- `V_1 × V_2 ≅ V × V` is sofic iff `V` is. Each of `V_1 × V_2`, `H_u` and `⟨V_2, u⟩` contains
  `g ⊗ 1 = u (1 ⊗ g) u^(-1)`, and the argument of Corollary 4.4 applies to each.
- So a fullness proof specific to `2V` needs `b, c` whose supports do not lie together in any one of the three.
  `⟨V_1, 1 ⊗ h, u⟩` is such a subgroup: `u` mixes the coordinates, `1 ⊗ h` is not in `H`, and by the same
  computation in the first coordinate `h ⊗ 1` is not in `⟨V_2, u⟩`.
