---
rg: 2
id: bs12-amenable-square-chain-induced-tower-proof
kind: route
title: Prepend a new bottom letter with an induced rank-one module, then turn the prepending tower into forward growth by taking its direct limit
target: bs12-extends-to-amenable-square-conjugation-chain
requires: []
---

Date: 2026-09-18. Written proof, not a Lean certificate. It uses only the
definition of an induced module and the facts that solvable groups and
directed unions of amenable groups are amenable.

Conventions. In a semidirect product `V rtimes K` with `V` a left
`Q[K]`-module, `(v,g)(w,h) = (v + g.w, gh)`, so `g v g^(-1) = g.v`. A
*chain of length `k`* in a group `K` is a tuple `(y_0,...,y_k)` with
`y_0` of infinite order and

    y_(j+1)^(-1) y_j y_(j+1) = y_j^2      (0 <= j < k).

## 1. The prepend functor

Let `K` be a group and `c in K` an element of infinite order. Let `Q_chi`
be `Q` with `c` acting by `1/2`, and put

    V(K,c) = Q[K] (x)_(Q[<c>]) Q_chi,     e = 1 (x) 1,     Phi(K,c) = V(K,c) rtimes K.

**Lemma 1.** (i) As a `Q`-vector space, `V(K,c)` has basis
`{g (x) 1 : g in T}` for a transversal `T` of `K/<c>` containing `1`. In
particular `e != 0`, so `e` has infinite order in `Phi(K,c)`.
(ii) `c^(-1) e c = e^2` in `Phi(K,c)`.
(iii) If `(y_0,...,y_k)` is a chain in `K` with `y_0 = c`, then
`(e, y_0, ..., y_k)` is a chain of length `k+1` in `Phi(K,c)`.
(iv) If `K` is solvable of derived length `d`, then `Phi(K,c)` is
solvable of derived length at most `d+1`.

*Proof.* (i) `Q[K]` is a free right `Q[<c>]`-module on `T`, so
`Q[K] (x)_(Q[<c>]) Q_chi` is free over `Q` on `T (x) 1`.
(ii) `c.e = c (x) 1 = 1 (x) chi(c) = e/2`, so `c^(-1).e = 2e`. With the
convention above, `c^(-1) e c = c^(-1).e = 2e`, which is `e^2` written
additively.
(iii) The relations among `y_0,...,y_k` hold in the complement `K`; the new
relation `y_0^(-1) e y_0 = e^2` is (ii); `e` has infinite order by (i).
(iv) `V` is abelian and normal with quotient `K`. ∎

**Lemma 2 (functoriality).** Let `f : K -> L` be an injective homomorphism
with `f(c_K) = c_L`. Then `V(f) : g (x) q -> f(g) (x) q` is a well-defined,
injective, `K`-equivariant linear map `V(K,c_K) -> V(L,c_L)` with
`V(f)(e) = e`, and `Phi(f)(v,g) = (V(f)v, f(g))` is an injective
homomorphism `Phi(K,c_K) -> Phi(L,c_L)` extending `f` on the complement.

*Proof.* `f` maps `Q[<c_K>]` onto `Q[<c_L>]` compatibly with `chi`, so
`V(f)` is well defined, and it is `K`-equivariant by construction. A
transversal `T` of `K/<c_K>` maps to a set of pairwise distinct cosets of
`<c_L>`: if `f(g)^(-1) f(g') in <c_L> = f(<c_K>)`, then
`g^(-1) g' in <c_K>` because `f` is injective. Extend `f(T)` to a
transversal of `L/<c_L>`; by Lemma 1(i) `V(f)` maps a basis injectively
into a basis. The formula for `Phi(f)` respects the multiplication because
`V(f)(g.w) = f(g).V(f)(w)`. ∎

## 2. The tower

Put `H_0 = Z = <z>` with the chain `(y^(0)_0) = (z)`. Given `H_k` with a
chain `(y^(k)_0, ..., y^(k)_k)`, put

    H_(k+1) = Phi(H_k, y^(k)_0),
    (y^(k+1)_0, ..., y^(k+1)_(k+1)) = (e, y^(k)_0, ..., y^(k)_k).

By Lemma 1, this is a chain of length `k+1`, and `H_k` is solvable of
derived length at most `k+1`.

**Lemma 3.** There are injective homomorphisms `iota_k : H_k -> H_(k+1)` with
`iota_k(y^(k)_j) = y^(k+1)_j` for `0 <= j <= k`.

*Proof.* `k = 0`: `iota_0(z) = e in H_1`. It is injective because `e` has
infinite order. Inductively, suppose `iota_k` is given. Since
`iota_k(y^(k)_0) = y^(k+1)_0`, Lemma 2 applies with `c_K = y^(k)_0` and
`c_L = y^(k+1)_0`, and gives `iota_(k+1) := Phi(iota_k) : H_(k+1) -> H_(k+2)`,
injective. It sends the bottom `e` to `e`, which is `j = 0`. For
`1 <= j <= k+1`, `y^(k+1)_j = y^(k)_(j-1)` lies in the complement, and
`iota_(k+1)` sends it to `iota_k(y^(k)_(j-1)) = y^(k+1)_(j-1) = y^(k+2)_j`. ∎

So the chains are compatible. The bottom is fixed, and each stage adds one
new letter at the **top** (the original generator `z` of `H_0`). The functor
itself only ever prepends at the bottom.

## 3. The theorem

Let `H_inf = lim_k (H_k, iota_k)`, and let `y_j` be the common image of
`y^(k)_j` for `k >= j`.

**Theorem.** `H_inf` is a countable, locally solvable, hence elementary
amenable, group, and `(y_j)_(j >= 0)` satisfies
`y_(j+1)^(-1) y_j y_(j+1) = y_j^2` for all `j >= 0`. The subgroup
`<y_0, y_1>` is isomorphic to `BS(1,2)` via `x_0 -> y_0`, `x_1 -> y_1`.

*Proof.* The `iota_k` are injective, so `H_inf` is the directed union of
copies of the solvable groups `H_k`; a directed union of amenable groups is
amenable. The relation with index `j` holds in `H_(j+1)`, hence in
`H_inf`. `y_0 = e` has infinite order in `H_1` and `iota` is injective.

`<y_0,y_1>` is a quotient of `BS(1,2) = Z[1/2] rtimes Z`, with
`x_0 = 1 in Z[1/2]`. Let `N` be the kernel.
* If `N cap Z[1/2]` contains `m/2^r != 0`, it contains
  `x_1^(-r) (m/2^r) x_1^r = m`, since conjugation by `x_1` doubles. So
  `y_0^m = 1`, which is false.
* Otherwise `N` injects into `Z`. If `(v,n) in N` with `n != 0`, then the
  commutator of `(v,n)` with `(1,0)` is `+-(2^(+-n) - 1)` times a power of
  two, which is a nonzero element of `N cap Z[1/2]`. That is excluded.

So `N = 1`. ∎

Setting `x_j = y_j` gives the claim.

## 4. Consistency with the chain obstruction

[[bg-shift-chains-die-in-residually-linear-alphabets]] says that forward
chains die in residually (periodic, linear, solvable) groups. Here:
* **Not solvable.** Each `H_k` is solvable, but `M = <y_j>` is perfect and
  lies in no `H_k`: `y_k` is not in `[H_k,H_k]`, since
  `H_k ->> H_(k-1) ->> ... ->> H_0 = Z` sends `y^(k)_k` to `z`. The
  commutator `y_k = [y_k, y_(k+1)]` only appears in `H_(k+1)`.
* **Not linear.** `H_1 = Q rtimes_(1/2) Z` is linear, but already `H_2`
  uses the infinite-dimensional module `V(H_1,e)`, with basis
  `H_1/<e>`. The obstruction needs `x_(j+1)` conjugate to its square with
  finitely many eigenvalues, and that is exactly what the induced module
  avoids.
* **Not residually solvable.** A nontrivial chain survives in `H_inf`, so it
  cannot be residually solvable.
* **Torsion-free.** Every `H_k` is torsion-free: a `Q`-vector space by a
  torsion-free group. So the descending-prime argument has nothing to act
  on.

## 5. The shift endomorphism and Baumslag--Gersten

`Phi` commutes with directed unions: if `K = U K_k` with `c in K_0`, then
`V(K,c) = U V(K_k,c)` by Lemma 2. So

    Phi(H_inf, y_0) = lim Phi(H_k) = lim H_(k+1) = H_inf.

Under this identification, the complement inclusion
`H_k -> Phi(H_k) = H_(k+1)` (on chains, `y^(k)_j -> y^(k+1)_(j+1)`) commutes
with the `iota`. So it induces an injective endomorphism

    theta : H_inf -> H_inf,     theta(y_j) = y_(j+1).

(The squares commute because `Phi(iota_k)` restricted to the complement is
`iota_k`.) Let `A = H_inf *_theta = < H_inf, tau | tau^(-1) h tau = theta(h) >`
be the ascending HNN extension. It is `(U_m tau^m H_inf tau^(-m)) rtimes <tau>`,
an increasing union of copies of `H_inf` extended by `Z`, so `A` is
elementary amenable.

**Corollary.** `BG = <a,t | (a^t)^(-1) a a^t = a^2>`, with `a^t = t^(-1) a t`,
maps to the elementary amenable group `A` by `a -> y_0`, `t -> tau`. The
image of `a` has infinite order.

*Proof.* `tau^(-1) y_0 tau = theta(y_0) = y_1`, and
`y_1^(-1) y_0 y_1 = y_0^2`. ∎

In particular the Magnus-kernel configuration `a_j -> tau^(-j) y_0 tau^j`
is a bi-infinite solution over an amenable alphabet that is faithful on the
piece `B_0 = BS(1,2)`, not only the one-sided solution with `x_j = 1` for
`j < 0`. Every finite quotient of `BG` kills `a`
([[baumslag-gersten-group-is-neither-linear-nor-self-similar]]), so the
amenable image cannot be replaced by a finite one. The obstruction theorem
shows it cannot be residually linear or residually solvable either.

## 6. Where the idea transfers

The forward equation `X^(-1) u X = u^2` in the unknown `X` has exponent sum
`0`, so it is singular and not solvable by Gerstenhaber--Rothaus. The tower
never solves it. It only solves the **backward** equation
`u^(-1) Y u = Y^2` in the unknown `Y`, which is linear in `Y` once `Y` lies
in an abelian normal subgroup: `(u^(-1) - 2).Y = 0`. It solves that
equation universally, with the rank-one induced module, and functorially.
The direct limit then converts repeated prepending into forward growth. The
general form of this for Magnus rewritings `W_0(a_0,...,a_n)` is recorded in
[[baumslag-gersten-elementary-amenable-quotient-keeps-a]].
