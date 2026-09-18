---
rg: 2
id: bounded-cluster-period-fixed-algebra-proof
kind: route
title: Proof that bounded cluster period builds an expander decomposition of the compressor-group graph
target: bounded-cluster-period-preserves-kazhdan-fixed-algebras
requires: []
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Items 1–3 are self-contained finite combinatorics. Item 4 imports two statements verbatim
from `research/artifacts/kun-thom-2608-06222-verified.md` (arXiv:2608.06222v1, the same
trust surface as `kun-thom-sofic-centralizer-normalization-citation`):

> [13, Theorem 1], as quoted on p. 4: "if H has property (T), then one can change
> o_𝒰(|Y_n|) edges so that the graphs become disjoint unions of graphs with a uniform
> positive Cheeger constant"

> Proposition 3.1: "Let Γ be an infranormal subgroup of G, and assume that both Γ and G
> are finitely generated. Let σ : G → 𝒮_𝒰 be a sofic representation. Assume that the
> generator graphs of both σ|_Γ and σ admit, after o_𝒰(|Y_n|) edge changes,
> decompositions into components with uniform positive Cheeger constants. Then
> σ(g)D_𝒰^{σ(Γ)}σ(g)^{-1} = D_𝒰^{σ(Γ)} for every g ∈ G."

## Conventions

Notation is that of the target.
- For a finite set `X` carrying edges labeled by a finite set `T` of permutations, and
  `A ⊆ X`, the boundary `∂A` is the number of pairs `(x, t)` with `x ∈ A`, `t ∈ T ∪ T^-1`
  and `t x ∈ X \ A`.
- The Cheeger constant is `min { ∂A / |A| : 0 < |A| <= |X|/2 }`.
- `o(·)` means `o_U(|Y_n|)`. Drop `n` from notation where harmless.
- `G'_n` is the edited `S`-graph of the frame, and `e_n = o(·)` is the number of changed
  edges. For a cluster `Q_i`, `r(i)` is the number of changed edges with an endpoint in
  `Q_i`, so `sum_i r(i) <= 2 e_n`.
- For `A ⊆ Q_i`, `∂_sigma^(i) A` counts the `sigma_n(s)^(±1)`-edges from `A` to `Q_i \ A`.
  Every `G'_n`-edge lies inside a cluster, so the `G'_n`-boundary of `A` is at most
  `∂_sigma^(i) A + r(i)`.

Fix words `w_s` in `S` with `u s u^-1 = w_s` in `L`, for `s ∈ S`, and let `m` be their
maximal length. Since `sigma` is a homomorphism to `S_U`, the defect set

```text
Def_n = { (y, s) : u_n sigma_n(s) u_n^-1 y != sigma_n(w_s) y }
```

has `|Def_n| = o(·)`. Let `Cr_n` be the set of pairs `(y, s)` with `sigma_n(s)^(±1) y` in a
cluster other than that of `y`. Every such edge is changed by the frame edit, so
`|Cr_n| <= 2 e_n = o(·)`.

## Item 1: the loss bound

Fix `i` and put `A_j = Q_i ∩ u_n^-1 Q_j`. These sets partition `Q_i`, and
`|A_(pi i)| = |Q_i| - ell(i)`.

**Leaks are rare.** Let `x ∈ A_j` and `s ∈ S` with `sigma_n(s) x ∈ Q_i \ A_j`. Put
`y = u_n x ∈ Q_j`. Then `u_n sigma_n(s) x = u_n sigma_n(s) u_n^-1 y` does not lie in
`Q_j`. So either `(y, s) ∈ Def_n`, or the `S`-path of `w_s` starting at `y` leaves the
cluster `Q_j`, and hence contains a pair in `Cr_n` at one of its `<= m` steps.

A pair `(z, s')` in `Cr_n`, a step `k <= m` and a letter `s` determine `y`, by reading the
prefix of `w_s` backwards. Also `x = u_n^-1 y`. The same holds for `s^-1`, with the words
`w_s^-1`. Summing over all `i` and `j`,

```text
sum_i sum_j ∂_sigma^(i) A_j  <=  2 ( |Def_n| + m |S| |Cr_n| )  =  o(·).          (L1)
```

**Expansion turns leaks into loss.**
- If `ell(i) <= |Q_i|/2`, apply the Cheeger bound in `G'_n` to `A = Q_i \ A_(pi i)`.
  This gives `h ell(i) <= ∂_sigma^(i) A + r(i) <= sum_j ∂_sigma^(i) A_j + r(i)`.
- Otherwise every `|A_j| < |Q_i|/2`. Each changed edge meets at most two of the `A_j`, so
  `h ell(i) <= h |Q_i| = h sum_j |A_j| <= sum_j ∂_sigma^(i) A_j + 2 r(i)`.

Summing over `i` and using (L1) gives `h sum_i ell(i) <= o(·) + 4 e_n`. Hence
`sum_i ell(i) = o(·)`.

## Item 2: bounded period builds the decomposition

Put `eps_n = sum_i ell_n(i) / |Y_n|`, so `eps_n -> 0` along `U` by item 1. Choose
`eta_n = sqrt(eps_n) + 1/n`. Then `eta_n -> 0` and `eps_n / eta_n -> 0` along `U`. Put
`lambda_n = (1 - eta_n)^-(p-1)` and `beta_n = lambda_n - 1 + 2 eta_n`, so both
`lambda_n -> 1` and `beta_n -> 0`. From now on, `n` ranges over the `U`-large set where
`eta_n <= 1/8`, `lambda_n <= 2` and `beta_n <= 1/8`.

**Step 1: good and bad clusters.** Call `i` *good* if `ell(i) <= eta |Q_i|`, and *bad*
otherwise. The bad clusters have weight `w(Bad) <= eps / eta -> 0`. For good `i`,

```text
|Q_(pi i)| >= |u_n Q_i ∩ Q_(pi i)| = |Q_i| - ell(i) >= (1 - eta) |Q_i|.            (G)
```

**Step 2: the core.** Let `O` be a `pi`-cycle of length `q <= p`.
- *All members good.* Following (G) around the cycle gives
  `(1 - eta)^(q-1) |Q_(pi i)| <= |Q_i| <= (1 - eta)^-1 |Q_(pi i)|`. So the sizes along `O`
  agree within the factor `lambda <= 2`, and `|Q_i| >= |B_O| / (2p)` for each member,
  where `B_O = union_(i in O) Q_i`.
- *Some member bad.* For each member `i`, let `b(i)` be the first bad member reached from
  `i` along `pi`, in `k <= q-1` steps through good members. By (G),
  `|Q_i| <= lambda |Q_(b(i))|`. Each bad member is `b(i)` for at most `p` members, so
  `|B_O| <= p lambda sum_(b in O bad) |Q_b|`.

Let `Core` be the union of the all-good cycles of length `<= p`, and `R = Y_n \ Core`.
Summing the second case over cycles,
`w(Core) >= w(Per_p) - 2p w(Bad) -> 1` by `BP_p`. So `|R| = o(·)`.

**Step 3: near-invariance of blocks.** For `i` on an all-good cycle,
- `|u_n Q_i \ Q_(pi i)| = ell(i) <= eta |Q_i|`;
- `|Q_(pi i) \ u_n Q_i| = |Q_(pi i)| - |Q_i| + ell(i) <= (lambda - 1 + eta) |Q_i|`.

So `|u_n Q_i Δ Q_(pi i)| <= beta |Q_i|`.

**Step 4: the edit of `u`.** Define `u'_n ∈ Sym(Y_n)` as follows.
- On each block `B_O` of `Core`, put `u'x = u_n x` whenever `u_n x ∈ B_O`. Let
  `X_O = { x ∈ B_O : u_n x ∉ B_O }`. The set `B_O \ u_n(B_O \ X_O)` has the same size as
  `X_O`, so map `X_O` onto it by any bijection.
- On `R`, put `u' = id`.

Then `u'` preserves each block and fixes `R` pointwise. A point `x ∈ Q_i ⊆ B_O` lies in
`X_O` only if `u_n x ∉ Q_(pi i)`, so `|X_O| <= sum_(i in O) ell(i)`. Hence

```text
|{ x : u'x != u_n x }| <= sum_i ell(i) + |R| = o(·).
```

Together with the frame edit of the `S`-edges, this is an `o(·)` edge change of the
`(S ∪ {u})`-graph. The edited graph `Γ'_n` has `G'_n` as its `S`-part and `u'` as its
`u`-part.

**Step 5: Cheeger constants.** Each block `B_O` and each cluster `Q_i ⊆ R` is a union of
components of `Γ'_n`.
- *A cluster `Q_i ⊆ R`.* Here `u'` is the identity, so the boundary of `A ⊆ Q_i` is its
  `G'_n`-boundary. It is `>= h|A|`.
- *A block `B_O`.* Let `A ⊆ B_O` with `0 < |A| <= |B_O|/2`, and put
  `a_i = |A ∩ Q_i| / |Q_i|` for `i ∈ O`. Let `delta = 1/8`. There are three cases.
  - (a) Some `a_i ∈ [delta, 1 - delta]`. The Cheeger bound in `Q_i`, applied to the
    smaller of `A ∩ Q_i` and `Q_i \ A`, gives
    `∂A >= h delta |Q_i| >= h delta |B_O| / (2p) >= h |A| / (8p)`.
  - (b) Every `a_i < delta`. Then `∂A >= sum_i h |A ∩ Q_i| = h |A|`.
  - (c) Every `a_i` lies outside `[delta, 1-delta]`, and some `a_i > 1 - delta`. They are
    not all `> 1 - delta`, since then `|A| > (1 - delta)|B_O| > |B_O|/2`. So going around
    the cycle there is an `i` with `a_i > 1 - delta` and `a_(pi i) < delta`. The points
    `x ∈ A ∩ Q_i` with `u_n x ∈ Q_(pi i)` number at least `(1 - delta - eta)|Q_i|`, and for
    them `u'x = u_n x`. At most `delta |Q_(pi i)| <= 2 delta |Q_i|` of their images lie in
    `A`. So `∂A >= (1 - 3 delta - eta)|Q_i| >= |Q_i|/2 >= |B_O|/(4p) >= |A|/(2p)`.

So every component graph has Cheeger constant `>= min(h/(8p), 1/(2p)) >= min(h,1)/(8p)`.
This proves item 2.

**Remark: why the period bound is needed.** Suppose `pi_n` is a single cycle of length
`N_n -> infinity` through equal-size clusters, with `u_n` mapping each cluster exactly onto
the next. Take the union of `N_n/2` consecutive clusters. Its boundary is the two
interfaces of `u`-edges, about `2|Q|`, against a mass of about `N_n|Q|/2`. So no uniform
expander decomposition of this shape exists. The same happens when cluster sizes drift
slowly along the cycle, and then the monotone functions `o_n` and `k_n` of Kun--Thom
Lemma 4.4 need not be nearly constant. Bounded period rules the model out: along a
`pi`-cycle of length `<= p`, an interface already carries a positive fraction of a block
(case (c)).

## Item 3: few clusters force bounded period

Let `|I_n| <= k` with `w_n(I_n) -> 1`. Pad and enumerate `I_n = {i_1, ..., i_k}` for
`U`-almost every `n`, and put `c_r = lim_U |Q_(i_r)| / |Y_n|`. Then `sum_r c_r = 1`. Let
`J = { r : c_r > 0 }`.

1. *The dominant targets of big clusters are big.* For `r ∈ J`, item 1 gives
   `|Q_(pi i_r)| >= |Q_(i_r)| - ell(i_r) >= |Q_(i_r)| - o(·)`. The clusters outside
   `{ i_r : r ∈ J }` carry weight `o(1)` in total, so `pi i_r = i_(f_n(r))` for some
   `f_n(r) ∈ J`, for `U`-almost every `n`.
2. *The map stabilizes.* There are finitely many maps `J -> J`, so `f_n = f` for
   `U`-almost every `n`.
3. *The map is a bijection.* For `r' ∈ J`, the sets `u_n Q_(i_r) ∩ Q_(i_r')` with
   `f(r) = r'` are disjoint subsets of `Q_(i_r')`, each of size `|Q_(i_r)| - o(·)` by item 1.
   Hence `c_r' >= sum_(f(r) = r') c_r`. Summing over `r'` gives
   `1 = sum_(r' in J) c_r' >= sum_(r in J) c_r = 1`. So every inequality is an equality.
   Any `r' ∉ f(J)` would have `c_r' = 0`, contradicting `r' ∈ J`. So `f` is surjective,
   hence a permutation of `J`.

Every `i_r` with `r ∈ J` then lies on a `pi_n`-cycle of length `<= |J| <= k`. So
`w_n(Per_(n,k)) >= w_n({ i_r : r ∈ J }) -> 1`, which is `BP_k`.

## Item 4: fixed-algebra invariance

Apply Proposition 3.1 with `Γ = L` and `G = H`. Its hypotheses hold as follows.
- `L` is finitely generated, being Kazhdan, and `H = <S ∪ {u}>`.
- `L` is infranormal in `H`: `P_L` contains `L` and `u`, which generate `H`.
- `sigma` is a sofic representation of `H`, and `sigma|_L` is one of `L`.
- The generator graph of `sigma|_L` decomposes after `o_U(|Y_n|)` edge changes into
  components of uniform positive Cheeger constant. This is [13, Theorem 1] for the Kazhdan
  group `L`, and it is the cluster frame itself.
- The generator graph of `sigma` for the generating set `S ∪ {u}` decomposes likewise.
  This is item 2 under `BP_p`, and items 3 and 2 under `FD_k`.

Proposition 3.1 then gives `sigma(g) D_U^(sigma(L)) sigma(g)^-1 = D_U^(sigma(L))` for every
`g ∈ H`. Nothing in this route uses property (T) of `H`.

## Item 5: FD is finite dimension

Lemma 2.3 (verbatim in the artifact) reads "D_𝒰^{σ(H)} = Π_{n→𝒰} D(𝒬_n)". Here
`D(Q_n)` is the algebra of functions constant on each cluster, and the lemma holds for the
component partition of the edited graph, which is our frame.

**FD_k gives dimension at most k.** Suppose `k` clusters `I_n` carry weight `-> 1`. Then an
element `[f_n]` is determined, in the trace norm, by the `k` values of `f_n` on the
clusters in `I_n`. So the dimension is `<= k`.

**Dimension at most k gives FD_k.** Let `dim D = d <= k`, with minimal projections
`e_1, ..., e_d` summing to `1`, and let `c_r = tr(e_r) > 0`.
- A projection in `prod_U D(Q_n)` is represented by indicators of unions of clusters.
  Given a representative `f_n`, take the clusters where `Re f_n > 1/2`; this changes it by
  `o(1)` in trace norm, since `||f_n - f_n^2||_2 -> 0`. So write `e_r = [1_(E_(r,n))]`,
  with `E_(r,n)` a union of clusters.
- *Some cluster of `E_(r,n)` is big.* Suppose that for `U`-almost every `n`, every cluster
  in `E_(r,n)` has weight `< c_r/3`. Adding clusters of `E_(r,n)` one at a time produces a
  union `F_n` of weight in `[c_r/3, 2c_r/3]`. Then `[1_(F_n)]` is a projection strictly
  between `0` and `e_r`, which contradicts minimality. So for `U`-almost every `n` there is
  a cluster `X_(r,n) ⊆ E_(r,n)` of weight `>= c_r/3`.
- *That cluster is almost all of `E_(r,n)`.* The projection `[1_(X_(r,n))]` is nonzero and
  lies below `e_r`, so it equals `e_r`. That is,
  `|E_(r,n) \ X_(r,n)| = o(|Y_n|)`.

So the `d <= k` clusters `X_(1,n), ..., X_(d,n)` carry weight `-> 1`. This is `FD_k`.
