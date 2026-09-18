---
rg: 2
id: higman-elementary-amenable-edge-images-collapse-proof
kind: route
title: The tower invariants are the orbit of a free action of the free group, so every nontrivial kernel word descends to a power of a single letter, and power pairs over elementary closures of locally indicable groups collapse
target: higman-elementary-amenable-edge-images-collapse
requires:
  - higman-bounded-derived-length-edge-images-collapse
  - higman-virtually-solvable-edge-images-collapse
  - nilpotent-edge-images-collapse-higman-quotients
artifacts:
  - experiments/higman-ea-edge-2026-09-18/state_action.py
  - experiments/higman-ea-edge-2026-09-18/state_action-output.txt
---

Conventions: `x^y = y^-1 x y` and `[x,y] = x^-1 y^-1 x y`. Fix a quotient `Q` of `H4` and `m >= 1`. Put
`alpha = a^m`, `gamma = c^m`, `P = 2^m`, `N_j = 2^(P^j)`, let `Phi` be free on `alpha, gamma`, let
`ev : Phi -> Q` be evaluation, and put `K = ker(ev)`, a normal subgroup of `Phi`. `A_m = ev(Phi)`.

We use the following, without change:
- **From `higman-bounded-derived-length-tower-chain-proof`** (the route of the target): flavours, kinds,
  heights, types `tau_r`, prefix sums `Pi_r`, invariants `S_r` (Step 1); the maps `sigma`, `sigma_*` and
  Lemmas A and B with its Corollary (Step 2); the subgroups `P_(>=0)`, `P_(d,>=0)` (Step 4).
- **From `higman-derived-length-three-edge-collapse-proof`** (cited there): the substitutions `iota_b`,
  `iota_d`, **Lemma 1** (`ev(iota_b(w)) = b^-1 ev(w) b` for `w in P_(>=0)`, mirrored for `d`), and
  **Lemma 3** (separation: if `delta != 0` is supported on `[h_1, oo)` with `||delta||_1 < N_(h_1)`,
  then `sum_h delta_h N_h != 0`).
- **From `higman-virtually-solvable-edge-images-collapse-proof`**: the conventions `S_(-1)`, `triv_j`; the
  concatenation maps `Theta_p` and their Lemma 1 (Step 1); the filtration
  `N_r = { u : S_j(u) = 0 for -1 <= j <= r-2 }` with its homomorphism `pi = S_(r-1)` and derivation
  `delta = S_r` (Step 2); formulas (2) and (3) and Lemma 2 (Steps 3–5). Step 8 below is a referee check
  of those steps.

Say that `u` has **level `r`** (in a given flavour) if `S_j(u) = 0` for `-1 <= j < r` and `S_r(u) != 0`,
that is, `u in N_(r+1)` and `S_r(u) != 0`.

## Step 1 (full types: the invariants are one orbit)

Work in flavour `b`: `alpha` has kind 1, `gamma` has kind 0, heights are `alpha`-heights. (Flavour `d`
is the mirror under `alpha <-> gamma`.)

**The state space.** Let `W` and `V` be the least sets with

```text
W = Z x Z[V]     (elements w = (h, A)),        V = Z[W]     (elements v = G),
```

where `Z[S]` is the free abelian group of finite formal sums on a set `S`. (Build them together by
recursion on nesting depth; every element is a hereditarily finite object.) Let `Phi` act on the right
of `W x V` by

```text
(w, v) . alpha^(+-1) = ( (h +- 1, A +- [v]), v ),        (w, v) . gamma^(+-1) = ( w, v +- [w] ).
```

The `+` and `-` maps are mutually inverse, so this is an action of the free group. Write `u . 0` for the
image of `0 = ((0, 0), 0)` under `u`, reading `u` from left to right.

**Meaning.** Read a word `u` letter by letter from `0`. Just before a letter `x` the state is
`((h, A), G)`, where `h` is the `alpha`-height, `A` is the signed sum of the full types of the earlier
`alpha`-letters, and `G` is the signed sum of the full types of the earlier `gamma`-letters. The
**full type** of `x` is `(h, A)` in `W` if `x` is a `gamma`-letter and `G` in `V` if `x` is an
`alpha`-letter. The action rule says exactly this: an `alpha^(+-1)` adds `+-1` to the height and
`+-[its full type]` to `A`; a `gamma^(+-1)` adds `+-[its full type]` to `G`. (Letter `x^(-1)` gets the
state before it, as in the tower route, so the definitions agree.)

**Truncations.** Define `tr_r` on `W` for even `r >= 0`, and on `V` for odd `r >= -1`:

```text
tr_(-1)(G) = *,                  tr_r(G)      = ( tr_(r-2)(G),      (tr_(r-1))_*(G) )   (r >= 1 odd),
tr_0((h, A)) = h,                tr_r((h, A)) = ( tr_(r-2)((h,A)), (tr_(r-1))_*(A) )   (r >= 2 even),
```

with `(tr_j)_*` the push-forward of formal sums.

**Lemma 1.1.** For every letter `x` of `u` and every level `r` of its parity, `tau_r(x) = tr_r(ft(x))`,
where `ft(x)` is the full type. Hence, with `u . 0 = ((h, A), G)`:

```text
S_(-1)(u) = h [*],     S_r(u) = (tr_r)_*(A)  (r odd),     S_r(u) = (tr_r)_*(G)  (r even).
```

*Proof.* Induction on `r`. `tr_(-1) = *` and `tr_0` is the height. For `r >= 1`,
`tau_r(x) = (tau_(r-2)(x), Pi_(r-1)(x))`, and `Pi_(r-1)(x)` is the signed sum of `[tau_(r-1)(y)]` over the
earlier letters `y` of the other kind. By induction this is `(tr_(r-1))_*` of the second component of the
state (`A` or `G`) before `x`, which is the relevant part of `ft(x)`. The formulas for `S_r` are the same
computation for a letter placed after `u`. ∎

**Lemma 1.2 (separation).** Two distinct elements of `W` (or of `V`) have distinct truncations at some
level. Consequently, for every finite set of elements of `W` (or `V`) there is `r_0` such that `tr_r` is
injective on it for all `r >= r_0` of the right parity.

*Proof.* The truncation `tr_(r+2)` determines `tr_r` (it is the first component). So once two elements
are separated at level `r`, they are separated at all higher levels of that parity, and the second
sentence follows from the first. For the first, induct on nesting depth.
- **Two elements `(h, A) != (h', A')` of `W`.** If `h != h'`, level 0 separates them. Otherwise
  `A - A' != 0`. By induction, some level `r_1` (odd) separates the finitely many elements of `V` in the
  support of `A - A'`, so `(tr_(r_1))_*(A - A') != 0`. Hence the second components at level `r_1 + 1`
  differ.
- **Two elements `G != G'` of `V`.** The same argument, with `G - G'` and a level `r_1` (even), gives
  separation at level `r_1 + 1`. ∎

**Corollary 1.3.** `u in N_oo := ∩_r N_r` (all `S_r(u) = 0`, `r >= -1`) iff `u . 0 = 0`.

*Proof.* If `u . 0 = 0`, Lemma 1.1 gives all `S_r(u) = 0`. Conversely, let all `S_r(u) = 0` and
`u . 0 = ((h, A), G)`. Then `h = 0`. Choose `r` so large that `tr_r` is injective on the supports of `A`
(odd `r`) and of `G` (even `r`) (Lemma 1.2). Then `(tr_r)_*(A) = 0` forces `A = 0`, and likewise
`G = 0`. ∎

**Rank.** Put `rank(0) = 0` and `rank(sum c_t [t]) = 1 + max { rank(t) : c_t != 0 }` for a nonzero formal
sum. Put `rank((h, A)) = rank(A)`, and let the rank of `G in V` be its rank as a formal sum. A nonzero
formal sum has rank `>= 1`.

**Proposition 1.4 (the action is free at 0).** Let `u = x_1^(e_1) ... x_k^(e_k)` be reduced, with `k >= 1`
blocks, `x_i in {alpha, gamma}` alternating, `e_i != 0`. After the first `i` blocks, the coordinate
changed by block `i` has rank exactly `i`, and the other coordinate has rank `i - 1`. In particular
`u . 0 != 0`, so **`N_oo = 1`**, in both flavours.

*Proof.* During an `alpha`-block, `v` is constant and `A` changes by `e [v]`; during a `gamma`-block, `w`
is constant and `G` changes by `e [w]`. (Here we take the `A`-part as the coordinate `w` changes; the
height `h` does not affect rank.)
- **`i = 1`.** From `0`, block 1 adds `e_1 [0]`, which is `e_1` times a basis element of rank 1. The
  other coordinate is still 0, of rank 0.
- **`i -> i + 1`.** Let `C` be the coordinate block `i` changed (rank `i`) and `D` the other (rank
  `i - 1`). Block `i + 1` adds `e_(i+1) [C]` to `D`, keeping `C` fixed. Every basis element in the
  support of `D` has rank at most `i - 2 < i = rank(C)`, so `[C]` is not in that support. Its coefficient
  in the new `D` is `e_(i+1) != 0`, and the new `D` has rank `1 + i`. `C` still has rank `i`.

After `k` blocks the changed coordinate has rank `k >= 1`, so it is nonzero and `u . 0 != 0`.
Corollary 1.3 gives `N_oo = 1`. ∎

So the tower invariants are **jointly faithful** on `Phi`: they are the coordinates of a free orbit.
`state_action.py` builds the action and checks it independently: all reduced words of length at most 10
give pairwise distinct states (118097 of them). So no nontrivial reduced word of length at most 20 fixes
`0`. Output: `state_action-output.txt`.

## Step 2 (the descent chain for an arbitrary kernel word)

Unlike the chain of the tower route, this chain does not start from a derived term. It starts from any
kernel word with vanishing kind-1 exponent sum, and there is no bad shift.

**Lemma 2.1 (clean shift).** Fix a flavour, let `x` be its kind-1 letter, let `u` have level `r >= 0`,
let `n >= 0`, and put `v = x^n u x^-n`. Then `S_j(v) = (Theta_p)_*(S_j(u))` for all `-1 <= j <= r`, where
`p = x^n`. So `v` has level `r`.

*Proof.* By Lemma 1 of the virtually-solvable route (concatenation, applied twice),
`S_j(v) = S_j(p) + (Theta_p)_* S_j(u) + (Theta_(pu))_* S_j(p^-1)`.
- **Even `j`.** `p` and `p^-1` have no kind-0 letters, so the outer terms vanish.
- **Odd `j`.** No letter of `p` or of `p^-1`, read on its own, has a kind-0 letter before it. So
  `S_j(p) = n [triv_j]` and `S_j(p^-1) = -n [triv_j]`. In `v` the letters of `p^-1` get the type
  `e_j = Theta_(pu)(triv_j)`. This satisfies `e_j = (e_(j-2), S_(j-1)(pu))`, with `e_(-1) = *`, and
  `S_(j-1)(pu) = S_(j-1)(p) + (Theta_p)_* S_(j-1)(u) = (Theta_p)_* S_(j-1)(u)`, since `j - 1` is even.
  For `j <= r` we have `j - 1 < r`, so `S_(j-1)(u) = 0`. Hence `e_j = triv_j` by induction, and
  `Theta_p` fixes `triv_j`. The outer terms are `n [triv_j] - n [triv_j] = 0`.
- **Level.** `Theta_p` is injective on each level, so `(Theta_p)_*` is injective on formal sums. ∎

(This is Lemma C of the tower route in the case where the lower invariants vanish: then `e_r = triv_r`,
and the exceptional `n` does not occur.)

**Lemma 2.2 (one step).** Let `u in K` have level `r >= 0` in flavour `d`. Choose `n` so large that
every `alpha`-letter of `v = gamma^n u gamma^-n` has `gamma`-height `>= h_*`, with `N_(h_*) > 2|v|`.
Put `u' = iota_d(v)`. Then:
- **(a)** `u' in K`;
- **(b)** if `r >= 1`, `u'` has level `r - 1` in flavour `b`;
- **(c)** if `r = 0`, `u'` has `alpha`-exponent sum `Y != 0` and `gamma`-exponent sum 0.

The mirror statement, from flavour `b` to flavour `d` through `alpha^n` and `iota_b`, also holds.

*Proof.* Such an `n` exists: heights grow like `n - c`, where `c` bounds the negative heights in `u`,
while `|v| = |u| + 2n` grows linearly and `N_(n-c)` doubly exponentially. By Lemma 2.1 (in flavour `d`,
where `x = gamma`), `v` has level `r`. In particular `S^d_(-1)(v) = 0`, so the `gamma`-exponent sum of
`v` is 0.
- **(a)** `v in K`, since `K` is normal. Its `gamma`-exponent sum is 0 and its `alpha`-letters lie at
  `gamma`-heights `>= h_* >= 0`, so `v in P_(d,>=0)`. Lemma 1 (mirror) gives
  `ev(u') = d^-1 ev(v) d = 1`.
- **Transfer.** Lemma A holds for `r >= -1`: in its proof, the base `r = -1` compares `*` with `*`, and
  the `Sums` line applies. So `S^b_j(u') = sigma_*(S^d_(j+1)(v))` for all `j >= -1`. At `j = -1` this
  reads `S^b_(-1)(u') = (sum_h c_h N_h) [*]`, where `S^d_0(v) = sum_h c_h [h]`.
- **(b)** For `j <= r - 2`, `S^d_(j+1)(v) = 0`, so `S^b_j(u') = 0`. At `j = r - 1 >= 0`, the Corollary of
  Lemma B gives `S^b_(r-1)(u') != 0`. Its hypotheses are the height bound and `r >= 1`.
- **(c)** The `alpha`-exponent sum of `u'` is `Y = sum_h c_h N_h`. Here `S^d_0(v) != 0`, the heights are
  `>= h_*`, and `sum |c_h| <= |v| < N_(h_*)`, so Lemma 3 gives `Y != 0`. The substitution `iota_d` keeps
  every `gamma`-letter, so the `gamma`-exponent sum of `u'` is that of `v`, which is 0. ∎

**Proposition 2.3 (chain).** Let `1 != u in K` have level `r >= 0` in flavour `f`. Apply Lemma 2.2
`r + 1` times, alternating flavours. The result is `z in K` whose exponent sums are `Y != 0` in one
letter `x_*` and 0 in the other. Hence **`x_*^Y in A_m'`**. The letter `x_*` is the kind-0 letter of the
flavour reached after `r` steps:

```text
f = d, r even:  x_* = alpha        f = d, r odd:  x_* = gamma
f = b, r even:  x_* = gamma        f = b, r odd:  x_* = alpha
```

*Proof.* Steps `1, ..., r` lower the level from `r` to 0, by (b), and alternate the flavour. Step
`r + 1` is (c), in the flavour `f_r` reached: the kind-1 letter of the next flavour, which is the kind-0
letter of `f_r`, gets exponent `Y != 0`. Every word stays in `K` by (a). Since
`z = alpha^Y mod Phi'` (or `gamma^Y mod Phi'`) and `ev(z) = 1`, we get `x_*^Y in ev(Phi') = A_m'`. ∎

## Step 3 (the parity flip)

**Lemma 3.1.** Fix a flavour and `r >= 0`. Let `u in K` have level `r`, let `x` be the letter of kind
`(r + 1) mod 2`, and let `n >= 1`. Then `u_2 = [u, x^n u x^-n]` lies in `K` and has level `r + 1`.

*Proof.* `u_2 in K` because `K` is normal. For the level, apply Steps 3–5 of the virtually-solvable
route with `r + 1` in place of its `r`. Its `r` is `>= 1`, as required there.
- **What those steps use.** They need `u in N_(r+1)` with `pi(u) = S_r(u) != 0`, and `x` of kind
  `(r + 1) mod 2`. They never use `u in Phi^(r+1)` otherwise. The one place where that route writes
  "`v in Phi^(r) <= N_r`, since `Phi^(r)` is normal" is covered by the normality of `N_(r+1)`
  (Step 8, item 1 below). In Step 4 there, the suffix computation uses only
  `S_(j-1)(u) = 0` for `j <= r`, which is `u in N_(r+1)`.
- **Conclusion.** Its Theorem's step shows that `delta([u, v]) = S_(r+1)(u_2) != 0`, where
  `v = x^n u x^-n`. It gets there by formulas (2) and (3) and the field Lemma 2. Also
  `u_2 in [N_(r+1), N_(r+1)] <= N_(r+2)`, so `u_2` has level `r + 1`. ∎

## Step 4 (the dichotomy)

**Theorem 4.1.** For every quotient `Q` and every `m >= 1`, either `K = 1` (so `A_m` is free on
`a^m, c^m`) or there are `Y, Y' != 0` with `a^(mY), c^(mY') in A_m'`. In the second case `A_m / A_m'` is a
quotient of `Z/Y x Z/Y'`, hence finite. Also `A_(mL) <= A_m'` for `L = lcm(Y, Y')`.

*Proof.* Let `K != 1`.
- **A kernel word in `Phi'`.** `K ∩ Phi' != 1`. Otherwise `K` embeds in `Phi / Phi' = Z^2` and is
  abelian, hence cyclic, because it is a subgroup of a free group. But a nontrivial normal cyclic
  subgroup of a free group of rank 2 does not exist: its normalizer would be cyclic.
- **Its level.** Pick `1 != u in K ∩ Phi'`. Then `S^b_(-1)(u) = 0`. By Proposition 1.4, `u` has some
  level `r >= 0` in flavour `b`.
- **The first letter.** Proposition 2.3 gives `x_*^Y in A_m'`. The letter `x_*` is `gamma` or `alpha`
  as `r` is even or odd.
- **The other letter.** Lemma 3.1 gives `u_2 in K` of level `r + 1` in flavour `b`. Proposition 2.3,
  applied to `u_2`, gives the other letter, since the parity has changed.
- **The rest.** Both `alpha^Y` and `gamma^(Y')` lie in `A_m'`, so `A_m / A_m'` is generated by two
  elements of finite orders dividing `Y` and `Y'`. Finally, `a^(mL) = alpha^L` and `c^(mL)` lie in the
  subgroup `A_m'`. ∎

**Corollary 4.2 (`T(k)` for all `k`, again).** If some `A_m` is solvable, then `Q = 1`.

*Proof.* A solvable `A_m` is not free, so iterating Theorem 4.1 gives `m = M_0 | M_1 | ...` with
`A_(M_(i+1)) <= A_(M_i)'`. Hence `A_(M_k) <= A_m^(k)`. If `A_m^(k) = 1`, then `a^(M_k) = 1` in `Q`, and
`<a^(M_k), c^(M_k)>` is cyclic. So `Q = 1` by item 1 of `higman-virtually-solvable-edge-images-collapse`
(or already by `T(2)`). ∎

This reproves `T(k)` without Steps 6–7 of the virtually-solvable route and without the witnesses `w_k`. It
still uses Steps 1–5 of that route, through Lemma 3.1.

## Step 5 (power pairs over elementary closures)

For a group `H = <x, y>` with a chosen generating pair, put `H_M = <x^M, y^M>`. Then `(H_M)_(M') = H_(MM')`.
Say `(H; x, y)` is **power-perfect** if `H_M / H_M'` is finite for every `M >= 1`. Power-perfectness passes
to `(H_M; x^M, y^M)`. It also passes to the image pair in any quotient `H/N`, since `(H/N)_M` is the image
of `H_M`, and an image of a finite abelianization is finite.

**Closure.** Let `X_0` be a class of groups closed under subgroups and isomorphism, containing the
trivial group. Define `X_(beta+1)` as the class of groups `G` that are either
- an extension (`N` normal in `G` with `N, G/N in X_beta`), or
- a directed union of subgroups in `X_beta`.

For limit `lambda`, put `X_lambda = ∪_(beta < lambda) X_beta`, and put `X = ∪_beta X_beta`. Then
`X_beta <= X_(beta+1)`: take `N = G`, or a one-term union.

**Lemma 5.1.**
- **(i)** Each `X_beta` is subgroup-closed.
- **(ii)** If `X_0` contains no nonabelian free group, neither does `X`.
- **(iii)** If `X_0` is also quotient-closed, so is `X`. Then `X` is closed under subgroups, quotients,
  extensions and directed unions.

*Proof.* Induction on `beta`. Limit stages are unions, so they inherit each property.
- **(i)** Let `L <= G`. If `G` is an extension of `N` by `G/N`, then `L ∩ N <= N` and
  `L/(L ∩ N) = LN/N <= G/N`. If `G = ∪ G_i` is directed, then `L = ∪ (L ∩ G_i)` is directed.
- **(ii)** Let `F_2 <= G`. By (i) it is enough to rule out `G = F_2`.
  - **Extension.** If `F_2 ∩ N = 1`, then `F_2` embeds in `G/N`. Otherwise `F_2 ∩ N` is a nontrivial
    normal subgroup of `F_2`. It is not cyclic, so it is free of rank `>= 2` and contains `F_2`. Either
    way `F_2` lies in a group of `X_beta`, a contradiction.
  - **Directed union.** `F_2` is finitely generated, so it lies in one member.
- **(iii)** Let `M` be normal in `G`.
  - **Extension.** `NM/M = N/(N ∩ M)` is a quotient of `N`, and `(G/M)/(NM/M) = G/NM` is a quotient of
    `G/N`.
  - **Directed union.** `G/M = ∪ G_i M/M` with `G_i M/M = G_i/(G_i ∩ M)`.
  - **Closure.** Given `N, G/N in X`, both lie in some `X_beta`, so `G in X_(beta+1)`. A directed union
    of members of `X` lies in `X_(beta+1)`, where `beta` is the supremum of their ranks. ∎

With `X_0 = {finite} ∪ {abelian}`, (iii) shows that `X` contains the class `EA` of elementary amenable
groups: `EA` is the smallest class containing `X_0` and closed under those four operations. Since `EA`
is itself closed under extensions and directed unions, `X = EA`. This is Chou's hierarchy; the argument
above does not need his theorem.

**Lemma 5.2 (power pairs).** Let `X_0` be as above. Assume:

> (**base**) every power-perfect pair `(H; x, y)` with `H in X_0` has a finite `H_M`.

Then every power-perfect pair `(H; x, y)` with `H in X` has a finite `H_M`.

*Proof.* Suppose not.
- **Minimal rank.** Choose a counterexample `(H; x, y)` with `H in X_alpha` and `alpha` minimal. Every
  `(H_M; x^M, y^M)` is also a counterexample: it is power-perfect, all of its power subgroups are power
  subgroups of `H` and so infinite, and `H_M in X_alpha` by Lemma 5.1(i).
- **`alpha = 0`** contradicts (base). A limit `alpha` is impossible, because `X_alpha` is a union of
  earlier stages. So `alpha = beta + 1`.
- **Directed union.** `H = ∪ G_i`, and `x, y` lie in a common `G_i`. Then `H = G_i in X_beta`,
  contradicting minimality.
- **Extension.** `N` is normal in `H`, with `N, H/N in X_beta`. The image pair in `H/N` is power-perfect
  and lies in `X_beta`, so by minimality some `(H/N)_M` is finite, of order `e` say. Then
  `x^(Me), y^(Me) in N`, so `H_(Me) <= N` lies in `X_beta`. But `(H_(Me); x^(Me), y^(Me))` is a
  counterexample, contradicting minimality. ∎

**The class used.** Let

```text
X_0 = {finite groups} ∪ {abelian groups} ∪ {locally indicable groups with no nonabelian free subgroup}.
```

Each of the three classes is subgroup-closed. None contains `F_2`: the first two are amenable, and the
third excludes it by definition.
- **Base.** Let `(H; x, y)` be power-perfect with `H in X_0`, and use `M = 1`. If `H` is finite, we are
  done. If `H` is abelian, then `H = H/H'` is finite. If `H` is locally indicable and `H != 1`, then `H`,
  being finitely generated, maps onto `Z`, so `H/H'` is infinite, a contradiction. So `H = 1`.
- **Result.** Lemma 5.2 applies to the closure `X`, which contains `EA` and contains no `F_2`.

## Step 6 (main theorem)

**Theorem 6.1.** Let `Q` be a quotient of `H4`. If the image `A` of `<a,c>` in `Q` lies in `X`, then
`Q = 1`. The same holds for `<b,d>`.

*Proof.* For each `M`, `A_M = <a^M, c^M> <= A` lies in `X` (Lemma 5.1(i)), so it is not free of rank 2
(Lemma 5.1(ii)). Theorem 4.1 at `m = M` then says `A_M / A_M'` is finite. So `(A; a, c)` is
power-perfect, and Lemma 5.2 gives a finite `A_M`, of order `e` say. Then `a^(Me) = 1` in `Q`, so
`<a^(Me), c^(Me)>` is cyclic, and `Q = 1` by item 1 of `higman-virtually-solvable-edge-images-collapse`.
The pair `<b,d>` follows by the automorphism `a -> b -> c -> d -> a`. ∎

The same proof works for any subgroup-closed, free-subgroup-free class `X_0` that satisfies (base).

## Step 7 (what `X` contains; trees)

- **Elementary amenable groups.** `EA <= X` by Lemma 5.1(iii). This includes locally solvable groups,
  which are directed unions of solvable groups. For the edge image itself this is no gain: `A` is
  2-generated, so if it is locally solvable it is solvable. The gain is for edge stabilizers in trees,
  which need not be finitely generated (see below). No height or shift choice uniform in the derived
  length is needed. The chain of Step 2 works with one kernel word at a time.
- **Amenable left-orderable groups.** Witte Morris (*Amenable groups that act on the line*,
  Algebr. Geom. Topol. 6 (2006)) proved that every amenable left-orderable group is locally indicable.
  Amenable groups contain no `F_2`, so these groups lie in `X_0`. Every group of orientation-preserving
  homeomorphisms of `R` is left-orderable. So `X_0` contains, for example, the Grigorchuk–Machì group
  (*On a group of intermediate growth that acts on a line by homeomorphisms*, Mat. Zametki 53 (1993)).
  That group has intermediate growth, so it is not elementary amenable: Chou showed that finitely
  generated elementary amenable groups have polynomial or exponential growth.
- **Piecewise linear groups.** Let `H` be a nontrivial finitely generated subgroup of `PL_+([0,1])`.
  - **A fixed point.** Let `x_0` be the infimum of the union of the supports of the generators. Every
    generator is the identity on `[0, x_0]`, so `H` fixes `x_0`.
  - **A nontrivial slope.** Some generator `g` moves points arbitrarily close to the right of `x_0`
    (there are finitely many generators). Being piecewise linear, `g` is linear on some `[x_0, x_0 + eps]`.
    Its slope `s` there is not 1, since otherwise `g` would be the identity there.
  - **A map onto `Z`.** By the chain rule, `h -> log h'(x_0^+)` is a homomorphism `H -> R`, and it is
    nonzero. Its image is a nonzero finitely generated torsion-free abelian group, so `H` maps onto `Z`.
    Hence `PL_+([0,1])` is locally indicable.
  - **Free subgroups.** By Brin–Squier (*Groups of piecewise linear homeomorphisms of the real line*,
    Invent. Math. 79 (1985)) it has no nonabelian free subgroup.
  - **Conclusion.** Every subgroup of `PL_+([0,1])` lies in `X_0`, in particular Thompson's group `F`,
    whether or not `F` is amenable.
- **Piecewise projective groups.** The same germ argument works for any group `H` of piecewise projective
  homeomorphisms of the line with finitely many pieces.
  - **The germ group.** Right germs at a common fixed point are germs of elements of `PSL_2(R)` fixing
    that point. Such a germ is trivial only if the element is the identity near the point.
  - **Point stabilizers.** The orientation-preserving part of the stabilizer of a point is conjugate to
    `Aff_+(R)`. A nontrivial finitely generated subgroup of `Aff_+(R)` maps onto `Z`, either through its
    multiplicative part or, if it consists of translations, because it is then free abelian.
  - **At infinity.** If the supports are not bounded below, use the germ at `-oo`, where the elements
    are affine.
  - **Conclusion.** Such groups are locally indicable. Monod (*Groups of piecewise projective
    homeomorphisms*, PNAS 110 (2013)) showed that his groups `H(A)` contain no nonabelian free subgroup and
    are non-amenable for suitable `A`. The finitely presented Lodha–Moore subgroup is another example.
    All of them lie in `X_0`. So the theorem also kills some **non-amenable** edge images.
- **Closure.** `X` also contains extensions and directed unions of all of these. Examples are
  `F`-by-`EA`, (Grigorchuk–Machì)-by-finite, and increasing unions of such groups.

**Trees.** Let `Q != 1` act on a tree without inversions and fix no vertex. By the tree gate (item 2 of
`nilpotent-edge-images-collapse-higman-quotients`), some edge is fixed by `a` and `c`, or by `b` and
`d`. If every edge stabilizer lies in `X`, that pair generates a subgroup of a group in `X`, which lies
in `X` by Lemma 5.1(i). Theorem 6.1 then gives `Q = 1`, a contradiction. So a nontrivial quotient of
`H4` never splits as an amalgam or HNN extension over subgroups in `X`, for example over elementary
amenable, locally solvable or amenable left-orderable subgroups.

## Step 8 (referee check of Steps 2–5 of `higman-virtually-solvable-edge-images-collapse-proof`)

These steps were checked line by line. The only changes are one additional fact and one weakening of a
hypothesis. Both are needed above.

1. **`N_r` is normal in `Phi`.** This is not stated there.
   - **Composition.** Lemma 1 of that route, applied to `p(uq) = (pu)q`, gives
     `Theta_(pu) = Theta_p ∘ Theta_u` on types occurring in words. For `u in N_r`, `Theta_u` is the
     identity on levels `<= r-1` (their Step 2).
   - **Normality.** For `j <= r-2`,
     `S_j(p u p^-1) = S_j(p) + (Theta_p)_* S_j(u) + (Theta_p)_*(Theta_u)_* S_j(p^-1) = S_j(p) + (Theta_p)_* S_j(p^-1) = S_j(p p^-1) = 0`.
2. **Steps 4–5 need only `u in N_r` with `pi(u) != 0`, not `u in Phi^(r)`.**
   - The membership `v in N_r` follows from item 1.
   - The suffix types `e_j` use only `S_(j-1)(u) = 0` for `j <= r-1`.
   - The field-lemma argument uses only `a != 0`.
   This is how Lemma 3.1 uses them.
3. **Formulas (1)–(3) are correct.**
   - **(1)** follows from their Lemma 1, because `Theta_u` translates level-`r` types by `S_(r-1)(u)`.
   - **(2)** follows from expanding `u^-1 v^-1 u v` with `delta(u^-1) = -t^(-a) X`.
   - **(3): the prefix and suffix.** `p = x^n` contributes `n E`. The suffix contributes
     `-n t^(theta a) E`, because `e_r = (triv_(r-2), theta(a))`.
   - **(3): semilinearity.** `Theta_p` acts on level `r` by `(tau, Pi) -> (Theta tau, theta(Pi))`, since
     `S_(r-1)(p) = 0` by parity. So `Theta_*` is `theta`-semilinear on the module `M_r`.
   - **(3): the fixed basis vector.** `Theta_p` fixes `triv_(r-2)`. Each step down adds `S_(j-1)(p) = 0`,
     again by parity. At the base, `*` is fixed, or height 0 is fixed because `S_(-1)(p) = 0` when `x` has
     kind 0.
4. **The `E`-coefficient.** In `Z = Theta_*(Z) + n E`, the coefficient of `E` on the right comes only from
   `tau = triv_(r-2)`, because `Theta` is injective and fixes `triv_(r-2)`. So `z_E = theta(z_E) + n`.
5. **Lemma 2 is correct**, including the edge cases.
   - **Constant `z`.** The support is empty, `L = 1`, and `theta(z) = z` gives `c = 0`.
   - **Support preserved.** Supports are preserved because `theta` is an injective renaming of variables,
     and partial derivatives commute with it as stated.

## Step 9 (calibration, scope, and the next case)

- **Calibration.**
  - **`Q = H4`.** `K = 1` and `A_m` is free. This is the first branch of Theorem 4.1, and nothing
    collapses.
  - **Without the Higman relations.** Take the group `<a, c | [a, c]>`. The kernel of `Phi -> Z^2` is
    `Phi' != 1`, yet `A/A' = Z^2` is infinite. So the dichotomy is false there. The proof uses the
    relations only through Lemma 1 (`iota_b`, `iota_d` evaluate to conjugates). Steps 1 and 3 are
    theorems about `Phi` alone. `state_action.py` checks Proposition 1.4 independently.
- **What is new.**
  - **Faithfulness.** The tower invariants are faithful (Proposition 1.4). So every nontrivial kernel
    word has a finite level, and the descent chain can start from it. The chain no longer needs a word
    from a derived term.
  - **Dichotomy.** This turns the collapse into a statement about all power pairs, and Lemma 5.2 lifts
    it through the elementary closure.
- **The next case.** Suppose `Q != 1`. Then its edge image `A` is not free, and it is power-perfect:
  - `a` and `c` have infinite order: if `a^e = 1`, then `<a^e, c^e>` is cyclic and `Q = 1`;
  - for every `M` there is `L` with `A_(ML) <= A_M'`;
  - no `A_M` is finite;
  - `A` lies outside `X`.

  So an amenable edge image must be a 2-generated amenable group with these properties. The remaining
  natural candidates are:
  - subgroups of topological full groups of minimal Cantor systems, whose derived subgroups are simple
    (Juschenko–Monod amenability, Matui simplicity);
  - other amenable groups built from simple or perfect pieces.

  The next step is to decide whether such a group can carry the Higman relations. Two routes:
  - find an invariant finer than abelianization that the descent chain controls. A candidate is the
    image of the chain word `z` in `A_M'/A_M''` or in a finite quotient of `A_M`;
  - build a power-perfect 2-generated amenable group, inside a topological full group, with
    `a, c` of infinite order.
