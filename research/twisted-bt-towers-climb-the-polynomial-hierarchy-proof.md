---
rg: 2
id: twisted-bt-towers-climb-the-polynomial-hierarchy-proof
kind: route
title: Store the universal variable in two coordinates the actor never moves, fire one controlled label per letter, and read the verdict off one coordinate
target: twisted-bt-towers-climb-the-polynomial-hierarchy
requires:
  - twisted-btb-clopen-action-is-type-a
  - twisted-brin-thompson-wp-equals-actor-orbit-problem
  - twisted-brin-thompson-finite-presentation-criterion
  - one-fp-simple-group-contains-every-brin-thompson-subgroup
---

Notation is the brick calculus of `twisted-btb-clopen-action-is-type-a`.
- A brick is `B(u)`, and `h_u` is prefix insertion.
- `(τ_g κ)(s) = κ(g^-1 s)`, and `τ_g τ_h = τ_(gh)`.
- Branches are `h_v τ_g h_u^-1`.
- `(TP1)` is `τ_g h_u = h_(g.u) τ_g` with `(g.u)(s) = u(g^-1 s)`, and
  `h_v h_w = h_(v*w)`.
- For a point `s ∈ S` and `x ∈ V`, `x_s` is the element acting as `x` on
  coordinate `s` alone. By the computation in `(a)` of
  `twisted-brin-thompson-wp-equals-actor-orbit-problem-proof`,
  `τ_g x_s τ_g^-1 = x_(gs)`.

## 1. Fiber calculus over two frozen coordinates

Let `G` act faithfully on `S`, and let `a != b` be points of `S`. Write
`κ = (κ_ab, κ_rest)` for the splitting `C^S = C^{a,b} × C^(S∖{a,b})`. Put
`H = Stab_G(a) ∩ Stab_G(b)`. For `t ∈ H`, `τ_t` preserves the splitting, acts
trivially on the first factor and permutes the coordinates of the second.

**(F1) Workspace moves.** Let `2V_ab` be the set of elements of `SV_G` whose
branches have label `1` and prefixes supported in `{a,b}`. Such an element acts as
`(κ_ab, κ_rest) ↦ (ḡ κ_ab, κ_rest)` for an element `ḡ` of Brin-Thompson `2V` on
`C^{a,b}`, and every `ḡ ∈ 2V` arises this way.

**(F2) Controlled labels.** Let `P ⊆ C^{a,b}` be clopen and `t ∈ H`. Define

```text
C_P(t)(κ_ab, κ_rest) = (κ_ab, τ_t κ_rest)   if κ_ab ∈ P,   and = κ otherwise.
```

Then `C_P(t) ∈ SV_G`.
- *Proof.* Write `P` as a disjoint union of bricks `B(v_i)` with `v_i` supported in
  `{a,b}`, and its complement as a union of bricks `B(v'_j)`. Since `t^-1` fixes
  `a` and `b`, `t.v_i = v_i`. So by `(TP1)`,
  `h_(v_i) τ_t h_(v_i)^-1 = τ_t h_(v_i) h_(v_i)^-1`, which is `τ_t` on `B(v_i)`.
- Hence `C_P(t)` has branches `h_(v_i) τ_t h_(v_i)^-1` on `B(v_i)` and identity
  branches on `B(v'_j)`. Each branch maps its brick onto itself, so the images
  partition the cube.

**(F3) Controlled moves on a third coordinate.** Let `r ∉ {a,b}`, `x ∈ V` and `P`
as above. Let `X_P(x)` act as `x_r` on `{κ_ab ∈ P}` and trivially elsewhere. Then
`X_P(x) ∈ SV_G`: refine the branches `h_(r↦w') h_(r↦w)^-1` of `x_r` by the bricks
`B(v_i)`, which is legitimate because `r ∉ supp v_i`.

**(F4) Fiberwise calculus.** Call `f` *fiberwise* if
`f(κ_ab, κ_rest) = (κ_ab, f_(κ_ab) κ_rest)`. The following are fiberwise:
- the elements `C_P(t)` and `X_P(x)`;
- `x_s` for `s ∉ {a,b}`, with constant fiber;
- products of fiberwise elements, with `(f f')_(κ_ab) = f_(κ_ab) f'_(κ_ab)`.

For `g ∈ 2V_ab` we have

```text
g^-1 C_P(t) g = C_(ḡ^-1 P)(t),       g^-1 X_P(x) g = X_(ḡ^-1 P)(x).     (F5)
```

*Proof of (F5).* `g^-1 C_P(t) g (κ_ab, κ_rest) = g^-1 (ḡκ_ab, τ_t^[ḡκ_ab ∈ P] κ_rest)`,
which equals `(κ_ab, τ_t^[κ_ab ∈ ḡ^-1 P] κ_rest)`. The same computation gives the
formula for `X_P(x)`.

## 2. Reversible circuits on the digits of `κ_a` in polynomial length

This is Birget's baker's-map idea, re-derived here in the form used.

**The elements.**
- The *baker* `β ∈ 2V_ab` has the two branches `h_(b↦d) h_(a↦d)^-1` on `B(a↦d)`,
  for `d ∈ {0,1}`. So
  `β(d κ'_a, κ_b) = (κ'_a, d κ_b)`, and
  `β^j(d_1…d_j κ'_a, κ_b) = (κ'_a, d_j…d_1 κ_b)`.
- For a permutation `π` of `{0,1}^3`, `Π_π ∈ 2V_ab` has branches
  `h_(a↦π(w)) h_(a↦w)^-1`, for `|w| = 3`. It applies `π` to the first three digits
  of `κ_a`.

**The shifted gate.** `β^-j Π_π β^j` applies `π` to digits `j+1, j+2, j+3` of `κ_a`
and fixes everything else, including `κ_b`. Its word length is `2j + O(1)`.

**Transpositions and gates.**
- With `π(d_1 d_2 d_3) = d_2 d_1 d_3`, the element `T_i = β^-(i-1) Π_π β^(i-1)`
  swaps digit positions `i` and `i+1`.
- Any gate (NOT, CNOT or Toffoli) on positions `p, q, s ≤ n` is realized as
  follows. Conjugate a gate on positions `1, 2, 3` (one `Π_π`) by a product of at
  most `3n` of the `T_i` with `i < n`. This moves positions `p, q, s` to the front.
- The cost is `O(n^2)` letters per gate.

**(R) Reversible circuits in polynomial length.** Given a reversible circuit `R` of
`s` gates on the first `n` digits of `κ_a`, one can compute in time `poly(s, n)` a
word of length `O(s n^2)`. The word is over the fixed finite set
`{β^±1, Π_π^±1}` and represents the element of `2V_ab` that applies `R` to those
digits and fixes all other digits of `κ_a`, and `κ_b`.

**Bennett form.** Let `c` be a Boolean circuit with `s` gates computing
`c : {0,1}^m → {0,1}`. There is a reversible circuit `R_c`, computable in
polynomial time, on the following digit positions of `κ_a`:
- position `1` (the target);
- positions `2 … n'` (scratch), with `n' = s + 1`;
- positions `n'+1 … n'+m` (the input `y`).

On every input whose positions `1 … n'` are all `0`, `R_c` writes `c(y)` in
position 1 and leaves positions `2 … n'+m` unchanged.

To build it:
1. `U` writes each gate value into its own scratch digit, using Toffoli and NOT
   gates.
2. A CNOT copies the output digit to position 1.
3. `U^-1` erases the scratch digits.

## 3. Lemma Q (one universal quantifier per layer)

**Hypotheses.**
- `G` acts faithfully on `S`, `SV_G` is finitely generated, and `Σ` is a finite
  generating set.
- `Y ⊂ G` is finite, and `a, b, r ∈ S` are distinct with `Y ⊆ Stab(a) ∩ Stab(b)`.
- `m` is a polynomial, and `Φ` is a polynomial-time map from pairs `(z,y)`, with
  `y ∈ {0,1}^m(|z|)`, to words over `Y`.
- `L' = {z : ∀y, Φ(z,y) r != r}`.
- `U* = {κ : κ(r) ∈ B(0)}` is a clopen set in the cube.
- Fix `x, x̃ ∈ V`: `x` swaps the cones `B(00)`, `B(10)` and `x̃` swaps `B(00)`,
  `B(01)`, both fixing the other two cones of length 2. Then `x B(0) != B(0)` and
  `[x, x̃] != 1`.

**Conclusion.** There are polynomial-time maps `z ↦ W_z, Z_z` to words over `Σ`
such that the following hold:
- `z ∈ L'` iff `W_z U* = U*` iff `Z_z = 1`;
- `z ∈ L'` iff `ι(W_z) ι(U*) = ι(U*)` iff `ι(Z_z) = 1`;
- `ι(W_z)` and `ι(Z_z)` are words of the same length over the fixed finite set
  `ι(K)` defined below, whose elements are supported in the fixed brick
  `B(q)`, `q = (a↦0)`.

Here `ι(f) = h_q f h_q^-1` on `B(q)`, extended by the identity off `B(q)`. By
`(TP1)`, the branch `h_v τ_g h_u^-1` goes to `h_(q*v) τ_g h_(q*u)^-1`. So `ι` is an
injective homomorphism `SV_G → SV_G`, and `ι(f)` fixes `ι(U) = h_q(U)` iff `f` fixes
`U`.

**Construction.** Fix `z`, and let `N = N(|z|)` bound the length of `Φ(z,y)`. Pad
with the empty letter so that `Φ(z,y) = φ_1(y) ⋯ φ_N(y)`, with each
`φ_j(y) ∈ Y ∪ {e}`.

*Letter-selection circuits.* For each `j ≤ N` and `t ∈ Y`, the bit
`β_(j,t)(y) = [φ_j(y) = t]` is computed by a Boolean circuit `c_(j,t)` with `z`
hard-wired. The circuit is produced in time `poly(|z|)` from the polynomial-time
machine for `Φ` by the standard tableau construction. Let `s` bound the sizes of
the circuits and put `n' = s + 1`. Place `y` in digit positions `n'+1 … n'+m` of
`κ_a`, and let `R_(j,t) = R_(c_(j,t))` be the Bennett form of §2.

*The elements.*

```text
E_(j,t) = R_(j,t)^-1  C_(B(a↦1))(t)  R_(j,t)          E_j = Π_(t ∈ Y) E_(j,t)
A       = E_1 E_2 ⋯ E_N
X_E     = ψ^-1 X_(B(a↦0))(x) ψ,      ψ = (x_0)_a^(n'-1)
W_z     = A X_E A^-1,                Z_z = [W_z, x̃_r]
```

Here:
- `(x_0)_a` is Thompson's generator `x_0` acting on coordinate `a`: it maps
  `B(00) → B(0)`, `B(01) → B(10)` and `B(1) → B(11)`.
- Hence `ψ` maps `B(0^n')` onto `B(0)`. By induction,
  `x_0(B(0^(i+1))) = B(0^i)` for `i ≥ 1`.
- `ψ ∈ 2V_ab`.
- Set `E = {κ_ab : κ_a ∈ B(0^n')}`.

The fixed finite set is

```text
K = { β^±1, Π_π^±1 (π ∈ Sym{0,1}^3), C_(B(a↦1))(t)^±1 (t ∈ Y),
      X_(B(a↦0))(x)^±1, ((x_0)_a)^±1, x̃_r^±1 }.
```

Every element of `K` is a fixed element of `SV_G`, and so a fixed word over `Σ`.

**Length.** Each `R_(j,t)` has length `O(s n^2)`, with `n = n' + m`, by `(R)`. So:
- `|A| = O(N |Y| s n^2)`;
- `|X_E| = O(n')`;
- `|W_z|, |Z_z| = O(N |Y| s n^2 + n')`.

This is polynomial in `|z|`, and the words are written down in polynomial time.

**Correctness.**
1. **Every piece is fiberwise.**
   - `R_(j,t)` and `ψ` lie in `2V_ab`.
   - By `(F5)`, `E_(j,t) = C_(P_(j,t))(t)` with `P_(j,t) = R̄_(j,t)^-1 B(a↦1)`, and
     `X_E = X_(ψ̄^-1 B(a↦0))(x) = X_E(x)`, since `ψ̄^-1 B(0) = B(0^n')`.
   - So `A`, `W_z` and `Z_z` are fiberwise by `(F4)`: none of them changes `κ_ab`.
2. **Fibers over `E`.** Let `κ_ab ∈ E` with input digits `y`.
   - By the Bennett form, `R̄_(j,t) κ_ab ∈ B(a↦1)` iff `β_(j,t)(y) = 1`. So the
     fiber of `E_(j,t)` is `τ_t^(β_(j,t)(y))`.
   - For each `j`, at most one `t ∈ Y` has `β_(j,t)(y) = 1`, and none does when
     `φ_j(y) = e`. So the fiber of `E_j` is `τ_(φ_j(y))`.
   - By `(F4)` and `τ_g τ_h = τ_(gh)`, the fiber of `A` is `τ_(Φ(z,y))`.
   - Put `g = Φ(z,y)`. The fiber of `W_z` is `τ_g x_r τ_g^-1 = x_(gr)`, and
     `gr ∉ {a,b}` because `g` fixes `a` and `b`.
   - The fiber of `Z_z` is `[x_(gr), x̃_r]`.
3. **Fibers off `E`.** The fiber of `X_E` is trivial, so the fibers of `W_z` and
   `Z_z` are trivial.
4. **Reading the verdict.** `U* = C^{a,b} × {κ_rest : κ_rest(r) ∈ B(0)}`.
   - A fiberwise `W_z` fixes `U*` iff every fiber fixes `{κ_rest(r) ∈ B(0)}`.
   - Off `E` this is automatic. Over `E`, the fiber `x_(gr)` fixes it iff
     `gr != r`: if `gr = r` it is `x_r`, and `x B(0) != B(0)`; if `gr != r` it does
     not touch coordinate `r`.
   - Likewise, `Z_z = 1` iff every fiber over `E` is trivial. Now
     `[x_(gr), x̃_r] = 1` iff `gr != r`: elements on different coordinates commute,
     and `[x, x̃] != 1`.
   - Every `y ∈ {0,1}^m` occurs as the input digits of some `κ_ab ∈ E`.
   - Hence `W_z U* = U*` iff `Z_z = 1` iff `Φ(z,y) r != r` for all `y`, iff
     `z ∈ L'`.
5. **Transport by `ι`.**
   - `ι(W_z)` fixes `ι(U*)` iff `W_z` fixes `U*`, and `ι(Z_z) = 1` iff `Z_z = 1`.
   - `ι(W_z)` and `ι(Z_z)` are the same words over `ι(K)`, and every element of
     `ι(K)` is supported in `B(q)`.
   - Each element of `ι(K)` is fixed, hence a fixed word over `Σ`. `∎`

**Frozen workspace for the next layer.** Let `S'` be the set of proper nonempty
clopen subsets of `C^S`. The clopens `a' = B(a↦10)` and `b' = B(a↦11)` are
disjoint from `B(q)`, so every element of `ι(K)` fixes them as points of `S'`. The
clopen `r' = ι(U*) = h_q(U*)` is proper, nonempty and contained in `B(q)`, so it is
distinct from `a'` and `b'`. So `(SV_G ↷ S', ι(K), a', b', r')` again satisfies the
hypotheses of Lemma Q, whenever the action of `SV_G` on `S'` is faithful and
`SV_(SV_G)` is finitely generated.

## 4. Lower bound by induction

Say that `(G ↷ S, Y, a, b, r)` is **`k`-hard** if the hypotheses of Lemma Q hold and,
for every language `N ∈ Π^p_k`, there is a polynomial-time `Φ` into words over `Y`
with `w ∈ N` iff `Φ(w) r = r`.

**Base, `k = 0`.** Take `G_0 = F ↷ D` and `a = 1/4`, `b = 1/2`, `r = 3/4`. Let
`Y = {σ}` with `σ ∈ F` supported in `[1/2, 1]` and `σ(3/4) != 3/4`. For `N ∈ P`,
let `Φ(w)` be the empty word if `w ∈ N` and `σ` otherwise. This `Φ` is computable
in polynomial time.

**Step.** Suppose `(G_k ↷ S_k, Y_k, a_k, b_k, r_k)` is `k`-hard. Let
`L' ∈ Π^p_(k+1)`.
- By Stockmeyer-Wrathall, `L' = {z : ∀y ∈ {0,1}^m(|z|), (z,y) ∉ N}` for a
  polynomial `m` and some `N ∈ Π^p_k`.
- `k`-hardness gives `Φ` with `(z,y) ∈ N` iff `Φ(z,y) r_k = r_k`. So
  `L' = {z : ∀y, Φ(z,y) r_k != r_k}`, which is exactly the form `(Q)`.
- Lemma Q then gives two things:
  - **(WP)** `z ∈ L'` iff `ι(Z_z) = 1` in `G_(k+1)`, so the word problem of
    `G_(k+1)` is `Π^p_(k+1)`-hard;
  - **(ST)** `z ∈ L'` iff `ι(W_z) r' = r'`, with `ι(W_z)` a word over
    `Y_(k+1) := ι(K)`, so `(G_(k+1) ↷ S_(k+1), ι(K), a', b', r')` is
    `(k+1)`-hard.

The side conditions of Lemma Q at every level hold by the following:
- `F ↷ D` is of type (A), as checked in
  `one-fp-simple-group-contains-every-brin-thompson-subgroup-proof`: faithful,
  finitely presented, stabilizers `F × F`, one orbit of 2-subsets.
- By induction with `twisted-btb-clopen-action-is-type-a`, each `G_k ↷ S_k` is
  faithful and of type (A).
- So `G_(k+1) = SV_(G_k)` is finitely presented and simple, by
  `twisted-brin-thompson-finite-presentation-criterion` and the setting of
  `twisted-brin-thompson-wp-equals-actor-orbit-problem`.

**Stabilizer membership at the orbit representative.** `G_k` has one orbit on
`S_k` for `k ≥ 1`: by item 3 of `twisted-btb-clopen-action-is-type-a`, a single
clopen `U` has the atom pattern `U != ∅ != U^c`. Fix `ρ` with `ρ r' = r_rep`. Then
`f r' = r'` iff `ρ f ρ^-1 r_rep = r_rep`, which is a linear-time substitution. So
the stabilizer part of `OP(G_k, S_k)` is `Π^p_k`-hard for `k ≥ 1`.

## 5. Upper bound by induction

**Base.** `OP(F, D)` is in `P`.
- Each generator of `F` is piecewise linear with dyadic breakpoints and slopes in
  `2^Z`.
- A word of length `l` is a piecewise-linear map with `O(l)` pieces, whose
  breakpoints and constants have `O(l)` bits. Composition with a generator adds
  `O(1)` breakpoints and `O(1)` bits.
- So the word is computable exactly in polynomial time, which gives the word
  problem. Evaluating it at a dyadic point `q` gives stabilizer membership.

**Step: `OP(G_(k+1), S_(k+1)) ∈ coNP^(OP(G_k, S_k))`.**
- **Word problem.** This is `(b)` of
  `twisted-brin-thompson-wp-equals-actor-orbit-problem`. Nontriviality has a
  polynomial-size witness, one path of the brick tracking, checked with
  polynomially many `OP(G_k)` queries.
- **Stabilizer of a fixed clopen `U`.** `U` is a fixed finite union of bricks, with
  supports in a finite set `D_U` and prefix lengths at most `p_U`.
  1. Run the brick tracking of the word `f` from
     `twisted-brin-thompson-wp-equals-actor-orbit-problem-proof` to a leaf state
     `(u, γ, v)`. There `f = h_v τ_γ h_u^-1` on `B(u)`.
  2. Refine further, with the same Refine step, until two things hold: `u` has
     prefix length `≥ p_U` at every coordinate of `D_U`, and so does `v`.
     Coordinates are located among the symbolic coordinates by `OP` queries. A
     refinement of `v` at `d` is a refinement of `u` at `γ^-1 d`.
  3. Then `B(u)` lies inside `U` or inside `U^c`, and `f(B(u)) = B(v)` lies inside
     `U` or inside `U^c`.
  4. The refined leaf bricks partition the cube. So `f U != U` iff some refined
     leaf crosses, meaning it has `B(u) ⊆ U` and `B(v) ⊆ U^c`, or the reverse.
  5. Such a leaf is a path of `O(l + |D_U| p_U)` binary choices. It is checked in
     polynomial time with polynomially many `OP(G_k)` queries.
- So the complement of `OP(G_(k+1), S_(k+1))` is in `NP^(OP(G_k,S_k))`.
- By induction, `OP(G_k, S_k) ∈ Π^p_k`. Then
  `coNP^(Π^p_k) = co(NP^(Σ^p_k)) = coΣ^p_(k+1) = Π^p_(k+1)`, because an oracle
  and its complement give the same relativized class.

**Conclusion.** For `k ≥ 1`, `WP(G_k)` and `OP(G_k, S_k)` lie in `Π^p_k`, and by §4
they are `Π^p_k`-hard. The yes-instances are the trivial words for WP, and the
stabilizer members for OP. This is the Theorem. `∎`

## 6. Remarks

- **PSPACE cap.** The step bound holds for any actor. So `OP ∈ PSPACE` passes to
  every finite tower, since `coNP^PSPACE = PSPACE`. An infinite tower is not a
  finitely generated group. This is the obstruction stated in the claim.
- **Why the frozen coordinates matter.** A controlled label at a coordinate `a`
  that the label moves carries the workspace digits to the coordinate `ta` on the
  controlled half. Later circuit gates then read the wrong coordinate, and the
  construction fails; this is why no free choice of `Y` works.
  - Lemma Q avoids this by requiring `Y ⊆ Stab(a) ∩ Stab(b)`.
  - The induction keeps this property through `ι`. Every hard word is supported in
    one brick, and the two clopens `a', b'` of the complementary brick are frozen
    points of the next actor.
- **What is not claimed.** This gives nothing beyond PSPACE, so
  `fp-simple-groups-with-arbitrarily-complex-word-problem` stays open. It does not
  say whether a single finitely presented simple group is PSPACE-hard. That would
  need a tower of unbounded height inside one finitely presented group.
- **Credit.** Baker's-map gates and circuit encoding are due to J.-C. Birget
  (arXiv:math/0310335, arXiv:1902.03852), whose work gives coNP-completeness of
  `nV`. The controlled labels `(F2)`, Lemma Q and the tower theorem were not found
  in the graph's imported literature and are treated here as new and unreviewed.
