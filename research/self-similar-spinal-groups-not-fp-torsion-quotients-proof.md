---
rg: 2
id: self-similar-spinal-groups-not-fp-torsion-quotients-proof
kind: route
title: A section cocycle on the free group halves reduced length and lifts infinite order through a filtration of the kernel
target: self-similar-spinal-groups-not-fp-torsion-quotients
requires: []
---

Notation as in `self-similar-spinal-groups-not-fp-torsion-quotients`.
Automorphisms of `X*` act on the left, `(gh)(v) = g(h(v))`. The section `g|_x`
is defined by `g(xw) = g(x) g|_x(w)`, and satisfies
`(gh)|_x = g|_{h(x)} h|_x`.

The alphabet is `S = (A\1) u (B\1)`. Write `s-bar` for the letter of an element
`s`, with `1-bar` the empty word. Let `F = F(S)`, `pi: F -> J` the evaluation,
and `N = ker pi`. Let `kappa: F -> A` send each `A`-letter to its element and
each `B`-letter to `1`. For `g in F` and `x in X` write `g(x) := kappa(g)(x)`.
Since `B` fixes level 1, `pi(g)(x) = g(x)`.

## Step 0. The base `A * B` and the subgroup `F_1`

Let `M_0` be the normal closure of the multiplication relators `s-bar t-bar (st)-bar^-1`
with `s, t` both in `A` or both in `B`. Then `F/M_0 = A * B`. `A` and `B` are
groups of automorphisms, so `M_0 <= N`.

Let `F_1 = ker kappa`. `A` acts faithfully on `X`. So if `pi(g) = 1`, the level-1
permutation `kappa(g)` is trivial. Hence `N <= F_1`.

For `g in F`, let `l(g)` be the length of the normal form of `g M_0` in
`A * B`. That is the length of the shortest word `g'` in `S` with `g' = g` mod `M_0`,
whose letters alternate between `A\1` and `B\1`.

## Step 1. The section cocycle

For a word `w = s_1^{e_1} ... s_n^{e_n}` (`s_j in S`, `e_j = +-1`) and `x in X`,
put `x_j := (s_{j+1}^{e_{j+1}} ... s_n^{e_n})(x)`. Define
`beta(b, x_0) = rho(b)-bar` and `beta(b, y) = omega_y(b)-bar` for `y != x_0`, and
`Phi_x(w) := prod_{j : s_j in B} beta(s_j, x_j)^{e_j}` (in order of `j`).

(a) *Well defined on `F`.* Inserting `s s^-1` or `s^-1 s` changes no `x_i` for
other positions, because `kappa(s s^-1) = 1`. If `s in A` it adds no letters. If
`s in B` the two letters are at positions with the same `x`-value, because
`kappa(s) = 1`, so they add `beta(s,x')^{+-1} beta(s,x')^{-+1}`, which reduces.

(b) *Cocycle.* `Phi_x(uv) = Phi_{v(x)}(u) Phi_x(v)`, directly from the
definition. In particular `Phi_x(uv) = Phi_x(u) Phi_x(v)` when `v in F_1`, so
`Phi_x` restricted to `F_1` is a homomorphism. Also
`Phi_{g^-1(x)}(g) Phi_x(g^-1) = Phi_x(1) = 1`.

(c) *Lifting.* `pi(Phi_x(w)) = pi(w)|_x`. This follows from
`(gh)|_x = g|_{h(x)} h|_x` by induction on the length. The base cases are
`a|_x = 1` for `a in A`, `b|_{x_0} = rho(b)`, `b|_y = omega_y(b)`, and
`(s^-1)|_x = (s|_{s^-1(x)})^-1 = (s|_x)^-1` for `s in B`.

(d) *Length.* `|Phi_x(w)| <=` the number of `B`-letters of `w`.

(e) *Surjectivity mod `M_0`.* `Phi_{x_0}(rho^-1(b)-bar) = b-bar` for `b in B`. For
`y != x_0` choose `c in A` with `c(x_0) = y`; then the word `c-bar^-1 b-bar c-bar`
lies in `F_1` and `Phi_{x_0}` of it is `omega_y(b)-bar`. So `Phi_{x_0}(F_1)`
contains every `B`-letter and every letter of `U_y omega_y(B)`. By
self-replication these generate `F` modulo `M_0`, so
`Phi_{x_0}(F_1) M_0 = F`.

## Step 2. The operator `Theta`

For `M` normal in `F` put
`Theta(M) := { w in F_1 : Phi_x(w) in M for all x in X }`.

(i) `Theta(M)` is a subgroup, because each `Phi_x` is a homomorphism on `F_1`.
It is normal: for `g in F` and `w in F_1`, (b) gives
`Phi_x(g w g^-1) = Phi_{w g^-1(x)}(g) Phi_{g^-1(x)}(w) Phi_x(g^-1)`. Here
`w g^-1 (x) = g^-1(x)`, so this is the conjugate of `Phi_{g^-1(x)}(w)` by
`Phi_{g^-1(x)}(g)`, which lies in `M`. Hence `g w g^-1 in Theta(M)`.

(ii) `Theta` is monotone, and `Theta(M) <= Phi_{x_0}^-1(M) n F_1`.

(iii) `M_0 <= Theta(M_0)`. By normality it suffices to check the generators.
An `A`-relator lies in `F_1` and has no `B`-letters, so `Phi_x` of it is empty.
A `B`-relator `b-bar b'-bar (bb')-bar^-1` lies in `F_1`, and all its
`x`-values equal `x`. `Phi_x` of it is `beta(b,x) beta(b',x) beta(bb',x)^-1`.
This is a multiplication relator of `B` (for `x = x_0`, as `rho` is a homomorphism) or of `A`, because
`omega_y` is a homomorphism: sections at a fixed vertex of automorphisms
fixing level 1 multiply. So it lies in `M_0`.

(iv) `Theta(N) <= N`. If `w in F_1` and every `pi(Phi_x(w)) = pi(w)|_x` is
trivial, then `pi(w)` fixes level 1 and has trivial sections, so `pi(w) = 1`.

Define `M_{k+1} := Theta(M_k)`. By (iii) and monotonicity,
`M_0 <= M_1 <= ...`. By `M_0 <= N` and (iv), every `M_k <= N`.

## Step 3. `U_k M_k = N`

We prove by strong induction on `l(w)` that each `w in N` lies in some `M_k`.
Let `w'` be the normal-form word of `w`, so `w = w'` mod `M_0` and
`|w'| = l(w) =: L`.

- `L = 0`: `w in M_0`.
- `L = 1`: `w'` is a single letter of a nontrivial automorphism, so
  `pi(w) != 1`. This case does not occur.
- `L >= 2`: `w' in N <= F_1`. For each `x`, `Phi_x(w') in N` by (c). By (d),
  `l(Phi_x(w')) <= |Phi_x(w')| <= ceil(L/2) < L`. By induction
  `Phi_x(w') in M_{k_x}`. With `k = max_x k_x`, `w' in Theta(M_k) = M_{k+1}`, and
  `w in w' M_0 <= M_{k+1}`.

## Step 4. Infinite order at every stage

`F/M_0 = A * B` has an element of infinite order: `A` and `B` are nontrivial,
because `A` is transitive with `d >= 2`, and `B != 1` by self-replication.
Suppose `g in F` has infinite order mod `M_k`. By (e) there are `h in F_1` and
`m in M_0 <= M_k` with `Phi_{x_0}(h) = g m`. If `h^j in M_{k+1}` for some `j >= 1`,
then by (ii) `Phi_{x_0}(h^j) = (gm)^j in M_k`, so `g^j in M_k`, a contradiction.
So `h` has infinite order mod `M_{k+1}`. By induction every `F/M_k` has an
element of infinite order.

## Step 4'. Free subgroups at every stage

Assume not `|A| = |B| = 2`. Then `A * B` contains a free subgroup of rank 2,
freely generated by the images of some `u, v in F`. Since `Phi_{x_0}` is a
homomorphism on `F_1` and `M_{k+1} = Theta(M_k) <= Phi_{x_0}^-1(M_k) n F_1`
(Step 2 (ii)), it induces a homomorphism `F_1 / M_{k+1} -> F / M_k`. Suppose
`u, v` freely generate a free subgroup modulo `M_k`. By (e) choose
`h_u, h_v in F_1` with `Phi_{x_0}(h_u) = u` and `Phi_{x_0}(h_v) = v` modulo
`M_0 <= M_k`. The induced map sends `<h_u, h_v> M_{k+1}` onto the free group on
`u M_k, v M_k`, sending generators to a basis. A 2-generated group with such a
map is free on those generators. So every `F/M_k` contains a non-abelian free
subgroup. In Step 5 the surjection `P -> F/M_k` then gives one in `P`, by lifting
a basis. That is item 3.

## Step 5. Consequences

*Marked limit.* The `M_k` increase to `N`, so `F/M_k -> J` in the space of
marked groups on `S`. That is item 1.

*Finitely presented covers.* Let `P = F(Y)/<<R>>` be finitely presented with
`p: P -> J` onto. Choose a homomorphism `lambda: F(Y) -> F` with
`pi(lambda(y)) = p(y)` for `y in Y`. Choose `mu(s) in F(Y)` with
`p(mu(s)) = pi(s)` for `s in S`. The finite set
`lambda(R) u { s^-1 lambda(mu(s)) : s in S }` lies in `N`, so it lies in some
`M_k` by Step 3 and monotonicity. Then `lambda` induces a homomorphism
`P -> F/M_k`. Its image contains every `s M_k`, so it is onto. A preimage of an
element of infinite order has infinite order, so `P` is not torsion. That is
item 2.

*Interior of the torsion locus.* If `J` were in that interior, a
neighbourhood `{ G : R' <= ker }` for some finite `R' <= N` would consist of
torsion groups. Every `F/M_k` with `R' <= M_k` is a non-torsion group in it.
[]

## Checks on the hypotheses

- *First Grigorchuk group.* `X = {0,1}`, `x_0 = 1`, `A = <a>`,
  `b = (a,c)`, `c = (a,d)`, `d = (1,b)`. So `omega_0(b) = omega_0(c) = a`,
  `omega_0(d) = 1`, `omega_0(B) = A`, and `rho = (b c d)` is an automorphism of `V_4`.
  Faithfulness of `B` is automatic: `B` is given as a group of automorphisms.
  We never need `omega_0` to be injective. (Here `d in ker omega_0`, but `d`
  acts nontrivially through its section `b` at `x_0`.)
- *GGS groups* `<a, t>` with `t = (a^{e_1}, ..., a^{e_{p-1}}, t)` and nonzero `e`.
  `A = <a> = C_p` is regular, `B = <t> = C_p`, and `omega_i(t) = a^{e_i}`
  generate `A`, with `rho = id`.
- The proof uses only that level-1 sections of `B` lie in `A` and at `x_0`
  lie in `B` through an automorphism `rho`. Deeper recursion of the sections, as in `d = (1,b)`, is
  handled by the induction in Step 3, never by a direct computation.
