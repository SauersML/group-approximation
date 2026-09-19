---
rg: 2
id: fpbs-mal-modp-promotion-certificates-are-fox-annihilators-proof
kind: route
title: Push the c-edges of the K-subgraph through the Fox derivative dc/db = 1 - c - cb, count first homology of the level graph, and pass to clopen graphings
target: fpbs-mal-modp-promotion-certificates-are-fox-annihilators
requires:
  - fpbs-mal-floor-iff-deep-promotion-floor
artifacts:
  - experiments/fpbs-modp-fox-floor-2026-09-17/foxfloor.py
  - experiments/fpbs-modp-fox-floor-2026-09-17/foxfloor_out.txt
  - experiments/fpbs-modp-fox-floor-2026-09-17/census.py
  - experiments/fpbs-modp-fox-floor-2026-09-17/census_out.txt
  - experiments/fpbs-modp-fox-floor-2026-09-17/census_big_p2.py
  - experiments/fpbs-modp-fox-floor-2026-09-17/census_big_p2_out.txt
---

# Proofs

## 0. Conventions

- `L = F(a, b)`, `c = b a b^-1 b^-1`, `K = <a, c>`, and `F` is any field.
- All actions are on the right: `v.(gh) = (v.g).h`.
  - A left action becomes a right one through `x.g := g^-1 x`.
  - This changes neither orbit relations, nor costs, nor freeness.
- For a finite right `L`-set `V`, the space `F[V]` is a right `F[L]`-module, with
  `[v] g = [v.g]`.
- `k_u(V) = dim_F { y in F[V] : y u = 0 }` with `u = 1 - c - cb`. In the matrix
  convention, this is `dim ker(I - P_c - P_cb)` with `(P_g)_{v, v.g} = 1`.
- Fox derivatives are left derivatives: `d(gh)/ds = dg/ds + g dh/ds` and
  `d(g^-1)/ds = -g^-1 dg/ds`.
- `Gamma(V)` is the Schreier graph, with an `s`-edge `v -> v.s` for `s in {a, b}`.
  `Y_K(V)` is the graph with an `a`-edge `v -> v.a` and a `c`-edge `v -> v.c`.
- `t = t(V)` is the number of components of `Y_K(V)`, that is, of `K`-orbits.
- `n = |V|`, and `V` is transitive.

## 1. The Fox computation

**Lemma 1.1.** `dc/da = b` and `dc/db = 1 - bab^-1 - bab^-2 = 1 - cb - c = u`.
Moreover `u (b - 1) = c - 1 + b - ba`.

*Proof.* `d(b a b^-1 b^-1)/db = 1 + ba d(b^-1)/db + b a b^-1 d(b^-1)/db`
`= 1 - b a b^-1 - b a b^-2`. In `L`, `b a b^-1 = c b` and `b a b^-2 = c`.
Expanding, `(1 - c - cb)(b - 1) = b - 1 - cb + c - cb^2 + cb = b - 1 + c - cb^2`,
and `cb^2 = ba`. []

**Lemma 1.2 (chains of paths).** Encode the 1-chains of `Gamma(V)` as
`F[V] e_a ⊕ F[V] e_b`. The path from `v` reading a word `w` then has chain
`[v] (dw/da) e_a + [v] (dw/db) e_b`, and the boundary is `∂(X_a, X_b) = X_a(a-1) + X_b(b-1)`.
Likewise for `Y_K(V)`, with `(a, c)` in place of `(a, b)`.

*Proof.* Induct on the length of `w`, using the product rule and `[v] g h = [v.g] h`.
A backwards `s`-edge from `v` is the edge `v.s^-1 -> v`, with chain `-[v] s^-1 e_s`,
which is `[v] d(s^-1)/ds`. The boundary of the edge `[v] e_s` is `[v.s] - [v]`. []

So `Z_1(Gamma) = { (X, Y) : X(a-1) + Y(b-1) = 0 }`. Since `Gamma` is connected, its
dimension is `2n - (n-1) = n + 1`. Likewise
`Z_1(Y_K) = { (x, y) : x(a-1) + y(c-1) = 0 }`, of dimension `2n - (n - t) = n + t`.

The graph map `f : Y_K -> Gamma` sends each `a`-edge to itself and the `c`-edge at `v`
to the path from `v` reading `b a b^-1 b^-1`. By Lemmas 1.1 and 1.2, it induces on
chains

```text
T(x, y) = (x + y b,  y u).
```

**Proposition 1.3.** `ker(T|Z_1(Y_K)) = { (-y b, y) : y u = 0 }`, which is isomorphic
to `{ y : y u = 0 }`. Hence

```text
codim_F T(Z_1(Y_K)) in Z_1(Gamma)  =  (n + 1) - (n + t - k_u)  =  1 - t + k_u.
```

*Proof.* `T(x, y) = 0` iff `y u = 0` and `x = -y b`.

For such a pair the cycle condition reads `-y b(a-1) + y(c-1) = y(c - 1 + b - ba)`.
By Lemma 1.1 this is `y u (b-1) = 0`, which holds automatically. So every `y` with
`y u = 0` gives exactly one element `(-yb, y)` of the kernel. []

`foxfloor.py` computes both sides of Theorem 1.4 below independently, by
elimination on `C_1`. It does this for 180 random transitive levels with
`n ≤ 40`, at `p = 2, 3, 5, 7, 1000003`: 900 pairs, 0 mismatches.

## 2. Counting extra edges at one level

**Theorem 1.4.** Let `Y` be the graph `Y_K(V)` plus `E` extra edges `e_i : v_i -> v_i.l_i`,
with `l_i in L`. Suppose that for some vertex `v` the labels of closed paths at `v`
generate `Stab(v)`, and that `Y` is connected. Then `E >= t - 1 + (1 - t + k_u) = k_u(V)`.

*Proof.*
1. Extend `f` to `Y` by sending `e_i` to the path from `v_i` reading a word for `l_i`.
   The label of a path in `Y` is the label of its image. Loops at `v` in `Gamma` are
   labelled by `Stab(v)`, and `pi_1(Gamma, v) -> Stab(v)` is an isomorphism, since
   `Gamma` covers the rose.
2. So `f_* : pi_1(Y, v) -> pi_1(Gamma, v)` is onto. Hence
   `f_* : H_1(Y;F) -> H_1(Gamma;F) = Z_1(Gamma)` is onto.
3. `Y` is `Y_K` (with `t` components) plus `E` edges, and it is connected. So
   `dim H_1(Y) = dim H_1(Y_K) + E - (t - 1)`, and `H_1(Y_K)` is a subspace of it.
4. Therefore `n + 1 = dim f_* H_1(Y) <= dim T(Z_1(Y_K)) + E - t + 1`.
5. Proposition 1.3 finishes the proof. []

**Remark 1.5 (sharpness and the non-abelian count).** Put `N = Stab(v)` and
`M = <<K ∩ N>>^L`. Then `M` is contained in `N`.
- The same argument without abelianizing gives the lower bound
  `E >= t - 1 + d(N/M)`.
- Conversely, `t - 1` connecting edges plus loops at `v` realize every element of
  `N`. So `min E` differs from `t - 1 + d(N/M)` only through the connecting term.
- `dim_F H_1(N/M; F) = 1 - t + k_u` is the mod-`p` shadow of `d(N/M)`. So Theorem 1.4
  is the best bound obtainable from first homology with field coefficients.

## 3. From graphings to levels

Let `X = lim V_m`, with `L`-equivariant surjections `pi_m : X -> V_m` and the inverse
limit of uniform measures. Assume the action is essentially free.

**Lemma 3.1 (clopen reduction).** Let `Phi` be a graphing inside `R_L` of cost `< eps`
with `R_K v Phi = R_L`, and let `delta > 0`. Then there are a level `m_0` and
finitely many pairs `(l_i, C_i)` with the following properties:
- each `l_i` is in `L`;
- each `C_i` is a union of fibres of `pi_{m_0}`;
- `sum mu(C_i) < eps + delta`;
- the maps `x -> x.l_i` on `C_i`, together with `a` and `c`, generate `R_L`.

*Proof.*
1. By essential freeness, every piece of `Phi` splits into countably many pieces of
   the form `x -> x.l` on `A_l`, and the cost is `sum_l mu(A_l)`.
2. For a.e. `x` the point `x.b` is reached from `x` by a finite path of `a^±`,
   `c^±` and piece moves. Enumerate these countably many formal paths. Choose a
   finite set `W` of them, using only labels from a finite set `S`, such that the
   set `G` of `x` joined to `x.b` by some path in `W` has `mu(G) > 1 - delta/4`.
   Let `R` bound their lengths.
3. Clopen sets are dense in the measure algebra of `X`. Pick clopen `C_l` with
   `mu(A_l Δ C_l) < eta` for `l in S`.
4. Let `G'` be the set of `x` joined to `x.b` by some path in `W` that uses `C_l` in
   place of `A_l`. It is a finite Boolean combination of translates of clopen sets,
   so it is clopen.
5. A point of `G \ G'` has one of the at most `R |W|` vertices of its witnessing path
   in some `A_l Δ C_l`. So `mu(G \ G') <= R |W| |S| eta`, because translations
   preserve the measure. Choose `eta` so that this is at most `delta/4`, and so that
   `|S| eta <= delta/4`.
6. Put `B = X \ G'`. This is clopen, with `mu(B) < delta/2`. Add the pair `(b, B)`.
7. Now every `x` is joined to `x.b`: through `W` if `x` is in `G'`, and by the new
   edge if `x` is in `B`. Since `a` lies in `K`, the new family generates `R_L`.
8. The cost is at most `sum_{l in S} mu(C_l) + mu(B)`, which is less than
   `eps + delta/4 + delta/2`.
9. There are finitely many clopen sets, so they are unions of fibres of one
   `pi_{m_0}`. []

**Theorem 2.** For every field `F`, `Q_0(X) >= limsup_m k_u(V_m)/|V_m|`.

*Proof.*
1. Take the family from Lemma 3.1 and any `m >= m_0`. Each `C_i` is a union of
   fibres of `pi_m`. Put `E_m = sum_i |pi_m(C_i)|`. Then
   `E_m / |V_m| = sum mu(C_i) < eps + delta`.
2. Build `Y` on `V_m` with the extra edges `w -> w.l_i` for `w in pi_m(C_i)`.
3. *`Y` generates `Stab(w)` at every `w`.* Let `l` be in `Stab(w)` and choose a free
   point `x` in `pi_m^-1(w)`, which has positive measure.
   - By generation there is a path in the graphing from `x` to `x.l`.
   - Its label `l'` satisfies `x.l' = x.l`, so `l' = l` by freeness.
   - The path projects to a closed path at `w` in `Y` with label `l`.
   - The same argument with `l` arbitrary shows `Y` is connected.
4. Theorem 1.4 gives `E_m >= k_u(V_m)`. So `k_u(V_m)/|V_m| < eps + delta` for all
   `m >= m_0`.
5. Let `delta -> 0` and `eps -> Q_0(X)`. []

**Corollary 2.1.** For the Bernoulli shift `rho` of `L`,
`r = Q_0(rho) >= sup_X kappa_F(X)`, the supremum over free profinite witnesses.

*Proof.* This is Theorem 2 together with Theorem M of
`fpbs-mal-promotion-cost-monotone-under-weak-containment`. That node is ESTABLISHED
on branch `claude/scale-agents-high-impact-erol9w`; it is not in this worktree.

That node states, for `j = 0`, that `Q_j(rho) = max Q_j(a)` over free actions `a`
of `F_2`, using Abért–Weiss. []

By `fpbs-mal-floor-iff-deep-promotion-floor`, the target implies `Q_0(rho) > 0`
(its part D0). So any certificate of the target yields one of D0.

## 4. p-towers

**Theorem 3.** Let `P` be the image of `L` in `Sym(V)`, and suppose `P` is a finite
`p`-group. Then `k_u(V) = 0` over `F_p`.

*Proof.*
- `F[V]` is an `F_p[P]`-module, and `u` acts through its image `ū` in `F_p[P]`.
- The augmentation of `ū` is `1 - 1 - 1 = -1`, which is not 0.
- For a finite `p`-group, `F_p[P]` is local with maximal ideal the augmentation
  ideal, which is nilpotent. So `ū` is a unit, and `y -> y u` is invertible. []

`F_2` is residually a finite `p`-group, for example through the Zassenhaus
filtration. So residual `p`-towers exist: their normal levels `V_m = L/N_m`, with
`p`-group quotients and `∩ N_m = 1`, give `kappa_{F_p} = 0` exactly, at every level.
The Sanov 3-adic census is consistent with the non-increase along `p`-layers recorded
in `fpbs-fibered-mod-p-certificates-refute-luck-approximation`, item 5:
`k_u/n` is `.125` and then `.037` at `p = 3`.

## 5. Item 4: the class of mod-p certificates is a Lück-approximation question

Source: A. Jaikin-Zapirain, *L2-Betti numbers and their analogues in positive
characteristic*, in Groups St Andrews 2017 in Birmingham, LMS Lecture Note Ser. 455,
Cambridge Univ. Press, 2019. Verbatim, from the text of Section 2.4:

> Let F be a group acting (on the right) on a finite set X and let K be a field. For
> every matrix A ∈ Mat_{n×m}(K[F]) let us define A^X : K[X]^n → K[X]^m,
> (x_1,...,x_n) ↦ (x_1,...,x_n)A. [...] rk_X(A) = dim_K Im A^X / |X| = n − dim_K ker A^X / |X|.

> Conjecture 2.4 (The sofic Lück approximation conjecture over K for a group G) Let
> {X_k} be a sofic approximation of G = F/N. Then (1) for every A ∈ Mat_{n×m}(K[F]),
> there exists the limit lim_{k→∞} rk_{X_k}(A); (2) the limit does not depend on the
> sofic approximation {X_i}; [...]

> Conjecture 2.4 holds when K is of characteristic 0. When K is of positive
> characteristic, the first and second parts of Conjecture 2.4 hold when G is amenable.

From the Introduction:

> If K is of positive characteristic, the parts (1) and (2) are only known when G is
> amenable and the part (3) when G is elementary amenable.

In that notation, with `A = u` a 1x1 matrix, `rk_V(u) = 1 - k_u(V)/|V|`.

**Proposition 5.1.** Let `p > 0`. If some free profinite witness has
`kappa_{F_p}(X) > 0`, then Conjecture 2.4 (1) or (2) fails for `G = F_2`,
`K = F_p`, `A = u`.

*Proof.*
1. The levels `V_m` of an essentially free profinite action of `L` form a sofic
   approximation of `F_2`: the proportion of `v` whose `R`-ball in `Gamma(V_m)` is
   not a tree tends to 0, for every `R`. The fibres of `pi_m` over such `v` are a
   decreasing sequence of sets, and their intersection is contained in the set of
   non-free points, which is null.
2. A residual `p`-tower is also a sofic approximation of `F_2`. On it
   `rk(u) = 1` at every level, by Theorem 3.
3. Along `X`, `liminf_m rk_{V_m}(u) = 1 - kappa < 1`.
4. So either the limit fails to exist along `X`, which breaks (1), or it exists and
   differs from 1, which breaks (2). []

For normal towers the same argument contradicts Conjecture 1.2 (1)–(2) of the same
survey.

**Remark 5.2 (characteristic 0).** Over `Q`, Conjecture 2.4 holds (quoted above), and
its part (3) gives `lim rk(u) = rk_{F_2}(u)`. This is 1 for `u ≠ 0`, because free
groups satisfy the strong Atiyah conjecture (Linnell). So `kappa_Q = 0` for every
witness, which agrees with the Linnell dead end already recorded on the target. The
kill in Item 4 of the claim uses only Proposition 5.1 and Theorem 3.

**Why this is the whole abelian class.** Consider any bound of the form "generation
at level `m` forces `E >= dim_F` (cokernel of the `K`-part in `H_1(Stab; F)`)".
- By Proposition 1.3 this is `t - 1 + (1 - t + k_u) = k_u`.
- Passing to a finer level `m' >= m` is the same functional at `m'`.
- Every coefficient field `F` has characteristic 0 or some `p`.
- So each member of the class is dominated by `kappa_F(X)` for some witness and some
  `F`. Proposition 5.1 and Remark 5.2 apply.

## 6. Census

`census.py`, `census_big_p2.py`, and outputs.
- Random Schreier levels: `k_u/n` decays like `O(1/n)` for `p = 2, 3, 5, 7` and
  `p = 1000003` (a proxy for char 0). At `p = 2`, `n = 1600..6400` gives
  mean `≤ .0004`.
- Cayley levels of `SL_2(Z/m)` and `PSL_2`, with the Sanov pair `[[1,2],[0,1]], [[1,0],[2,1]]`
  and with random pairs:
  - the Sanov 3-adic tower gives `.29, .069, .027` at `p = 2`;
  - the non-nested `PSL_2(F_q)`, `q ≤ 23`, gives `.011` to `.064` at `p = 2`.
- These values are small `O(1)` fractions that fluctuate with `q`. They are not
  witnesses: the family is not nested.
- No nested tower computed has `k_u/n` bounded away from 0.
