---
rg: 2
id: rank-two-bs-model-roots-need-infinite-order-witnesses-proof
kind: route
title: Proof that Baumslag--Solitar roots in a Magnus piece need infinite-order, non-metabelian witnesses, that solvable (AA) and (AA_G) coincide, and that the rank-two model G_2 is residually finite
target: rank-two-bs-model-roots-need-infinite-order-witnesses
requires: []
artifacts:
  - experiments/one-relator-rank-two-model-2026-09-17/rewrite.py
  - experiments/one-relator-rank-two-model-2026-09-17/rewrite.out
  - experiments/one-relator-rank-two-model-2026-09-17/lis.g
  - experiments/one-relator-rank-two-model-2026-09-17/lis.out
  - experiments/one-relator-rank-two-model-2026-09-17/search_window.py
  - experiments/one-relator-rank-two-model-2026-09-17/search_window.out
  - experiments/one-relator-rank-two-model-2026-09-17/verify_wreath.py
  - experiments/one-relator-rank-two-model-2026-09-17/verify_wreath.out
---

Proof of [[rank-two-bs-model-roots-need-infinite-order-witnesses]].
Notation is as in the claim: `x^s = s^(-1) x s` and
`[x,y] = x^(-1) y^(-1) x y`.

By Reidemeister--Schreier, `N = ker(G -> Z)` (with `a -> 0`, `t -> 1`) has the
presentation `<a_k (k in Z) | W_j (j in Z)>`. Here `W_j` is `W_0` with every
index shifted by `j`. By Magnus, each piece `B_j = <a_j..a_(j+n) | W_j>`
embeds in `N`, and so does each subgroup `F_- = <a_0..a_(n-1)>`,
`F_+ = <a_1..a_n>`. For `G_2` we have `n = 2` and
`W_0 = a_2^(-1) u a_2 u^(-2)` with `u = [a_0,a_1]`.

**Britton fact used throughout.** `B_0` is the HNN extension of `F(a_0,a_1)`
with stable letter `a_2`, associated subgroups `A = <u>` and `A' = <u^2>`,
and `a_2^(-1) u a_2 = u^2`. The word `v = a_2 u a_2^(-1)` contains a pinch
only if `u` lies in `A' = <u^2>`. That is false in the free group, because
`u` is not a proper power. So `v` is Britton-reduced of stable length 2, and
`v` is not in `F_-`. Also `v^2 = a_2 u^2 a_2^(-1) = u`.

## A. G_2 is an ascending HNN extension of F_3

The exponent sum of `a` in the relator is 0, because `u` and the conjugate of
`u` both have `a`-exponent 0. So we may also rewrite with `a` as the stable
letter, using letters `y_e` (conjugates of `t` by powers of `a`).
`rewrite.py` does this and prints the result in `rewrite.out` (it labels the
letters `x0..x3`). The rewritten relator `W'` is a word of length 16 in four
consecutive letters. One extreme letter occurs exactly once, with exponent
`+1`; after reindexing call it `y_0`. The other extreme occurs 4 times.

Solve `W' = 1` for `y_0`. This gives `y_0 = P(y_1,y_2,y_3)` for a word `P`.
Hence, by Tietze, every piece `<y_e..y_(e+3) | W'_e>` is free on
`y_(e+1), y_(e+2), y_(e+3)`. The kernel of the map `G -> Z` given by `a` is
therefore the increasing union of free groups of rank 3. Conjugation by the
appropriate power of `a` maps `y_e` to `y_(e-1)`. On
`F = F(y_1,y_2,y_3)` it induces the endomorphism

    phi(y_1) = P(y_1,y_2,y_3),   phi(y_2) = y_1,   phi(y_3) = y_2.

This endomorphism is injective because the pieces embed (Magnus). So
`G_2 = <F, a | a^(-1) f a = phi(f)>` is an ascending HNN extension of `F_3`.
Borisov--Sapir (Invent. Math. 160 (2005) 341--356) prove that every ascending
HNN extension of a finitely generated free group is residually finite. So
`G_2` is residually finite, hence sofic.

Peelability in the `t`-coordinate is read off the same output. The extreme
letter occurs twice, with exponents `-1` and `+1`. Those are exactly the two
syllables `a_2^(-1)` and `a_2` of `W_0`. This is the hypothesis of
[[peelable-extreme-one-relator-groups-are-sofic]]. In the `a`-coordinate the
single occurrence of `y_0` is trivially peelable. `[machine-checked]` for the
rewriting; the rest is standard.

## B. Root lemma

Let `rho` be a homomorphism defined on `B_0` (or on any group containing it).
Suppose `g^(-1) c g = c^k` with `|k| >= 2`, and put `r = g c g^(-1)`. Then

    r^k = g c^k g^(-1) = g (g^(-1) c g) g^(-1) = c.

Assume `rho(c)` has finite order `m`. The element `rho(c^k)` is conjugate to
`rho(c)`, so it also has order `m`. Hence `gcd(k,m) = 1`. Choose `k'` with
`k k' = 1 mod m`. The element `rho(r)` is conjugate to `rho(c)`, so it has
order `m`. Therefore

    rho(r) = rho(r)^(k k') = rho(r^k)^(k') = rho(c)^(k').

So `rho(r)` lies in `<rho(c)>`, which is contained in `rho(F_-)` whenever
`c` is in `F_-`. If `rho` has periodic or locally finite image, then
`rho(c)` is torsion and the conclusion applies.

**Profinite-closure consequence.** Let `Q = rho(G)` be finitely generated.
Suppose `rho(r)` is not in `rho(F_-)`, and that `rho(F_-)` is closed in the
profinite topology of `Q`.

1. Closedness gives a finite-index subgroup `H` of `Q` that contains
   `rho(F_-)` but not `rho(r)`.
2. Let `K` be the normal core of `H`. Then `P = Q/K` is finite.
3. The composite `B_0 -> P` sends `c` to an element of finite order, and it
   still separates `r` from `F_-`, because `H/K` contains the image of `F_-`
   but not the image of `r`.
4. This contradicts the lemma.

By Mal'cev, every subgroup of a virtually polycyclic group is closed in the
profinite topology. So no virtually polycyclic quotient separates `r` from
`F_-`.

**For `G_2`.** Take `g = a_2`, `c = u`, `k = 2`, so `r = v`. By the Britton
fact, `v` is not in `F_-`. `G_2` is finitely generated and residually finite
by A. If `F_-` were closed in its profinite topology, the argument above with
`rho = id` would give a finite quotient separating `v` from `F_-`,
contradicting the lemma. So `F_-` is not profinitely closed in `G_2`.

## C. Metabelian quotients of G_2

Let `pi : G_2 -> M` be a homomorphism with `M'` abelian.

In `G`, `a_0^(-1) a_2 = a^(-1) t^(-2) a t^2 = [a, t^2]`, so `z = [a,t^2]`
lies in `G'`. Also `u = [a_0,a_1]` lies in `G'`. Since `a_2 = a_0 z`,

    v = a_2 u a_2^(-1) = a_0 (z u z^(-1)) a_0^(-1).

Now `pi(z)` and `pi(u)` both lie in the abelian group `M'`, so they commute.
Therefore `pi(v) = pi(a_0) pi(u) pi(a_0)^(-1)`, which lies in `pi(F_-)`.

So a solvable witness that separates `v` from `F_-` has derived length at
least 3.

In any witness at `E_- = {v}`, B shows that `pi(u)` has infinite order. The
subgroup `<pi(u), pi(a_2)>` is a quotient of
`BS(1,2) = Z[1/2] ⋊ Z = <u, a_2 | a_2^(-1) u a_2 = u^2>` in which `u` has
infinite order. Every such quotient is faithful. To see this, let `K` be a
nontrivial kernel.

* If `K` meets `Z[1/2]` nontrivially, then it contains some `m/2^j` with
  `m ≠ 0`. It then contains `m`, i.e. `u^m`, so `u` has finite order.
* Otherwise `K` embeds in `Z`, so `K = <x>` with `x` acting on `Z[1/2]` by
  `2^e` for some `e ≠ 0`. Then `[x,u]` is a nonzero element of
  `K ∩ Z[1/2] = 0`, a contradiction.

The non-closedness of `pi(F_-)` in `pi(G_2)` is B applied to
`rho = pi`. `[written proof]`

## D. Kaloujnine--Krasner induction

Let `rho : N -> L` be a homomorphism. Let `Z` act on `L^Z` by
`(s f)(j) = f(j+1)`, and put

    pi(a) = (rho(a_j))_j  in L^Z,    pi(t) = s  in L^Z ⋊ Z,

with the action arranged so that `pi(t)^(-k) f pi(t)^k = (j -> f(j+k))`.

* **Coordinates.** `pi(a_k) = pi(t)^(-k) pi(a) pi(t)^k` has `j`-th coordinate
  `rho(a_(j+k))`.
* **Well defined.** The relator `w` of `G` equals `W_0(a_0..a_n)` in
  `F(a,t)`. Its image is `W_0(pi(a_0),...,pi(a_n))`, whose `j`-th coordinate
  is `W_0(rho(a_j),...,rho(a_(j+n))) = rho(W_j) = 1`. So `pi` is a
  homomorphism `G -> L^Z ⋊ Z`.
* **Transfer.** `pi(N)` lies in the base `L^Z`, and the coordinate map
  `ev_0 : L^Z -> L` is a homomorphism with `ev_0 ∘ pi|_N = rho`.
  - If `rho(x)` is not in `rho(F_-)`, then `pi(x)` is not in `pi(F_-)`,
    because `ev_0(pi(F_-)) = rho(F_-)`.
  - The same holds for `F_+`, and for survival (`rho(x) ≠ 1` implies
    `pi(x) ≠ 1`).
  - So every (AA) witness `rho` yields the (AA_G) witness `pi(G)` for the
    same finite sets.
* **Amenability.** If `L` is solvable of length `d`, then so is `L^Z`, and
  `L^Z ⋊ Z` has length at most `d+1`. If `rho(a_k) = 1` for all `k` outside
  a finite set, then `pi(a)` has finite support. In that case `pi(G)` lies in
  the restricted wreath product `L wr Z`, which is amenable whenever `L` is.
* **Converse.** An (AA_G) witness restricted to `N` is an (AA) witness, with
  the same derived-length bound.

So solvable (AA) holds iff solvable (AA_G) holds, and finitely supported
amenable (AA) implies (AA_G). The gap left open in
[[magnus-prepend-towers-are-amenable-quotients-of-the-group]] can therefore
only come from configurations that are not finitely supported and whose
alphabets have amenable groups with non-amenable unrestricted powers.

The final statement of the claim's "Not decided" item follows. Solvable
(AA_G) for all finite `E` means that for each finite `E` some term
`N ∩ G^(d)` avoids the finitely many required non-memberships. If some
nontrivial `x` in `B_0` lies in every `G^(d)`, then no solvable quotient
keeps `x`. `[written proof]`

## E. Certificate

Put `rho(a_0) = M0`, `rho(a_1) = M1`, `rho(a_2) = M2`, and `rho(a_k) = I`
otherwise, with

    M0 = [[1,-1,-1],[0,1,-1],[0,0,1]],
    M1 = [[1,0,0],[0,-1,1],[0,0,-1]],
    M2 = diag(1,2,2).

**Relations.** For `rho` to define a homomorphism on `N` we need every
`W_j`. `W_j` involves only `a_j, a_(j+1), a_(j+2)`, so only
`j = -2,...,2` are non-vacuous.

* `j = -2`: `[I,I] = I`.
* `j = -1`: `[I,M0] = I`.
* `j = 2`: `[M2,I] = I`.
* `j = 1`: `[M1,M2] = I` is needed. It holds because `M2` is scalar on
  `span(e_2,e_3)`, which `M1` preserves, and `M1` fixes `e_1`.
* `j = 0`: `M2^(-1) U M2 = U^2` is needed, where `U = [M0,M1]`.

A direct multiplication gives `U = [[1,2,1],[0,1,0],[0,0,1]] = I + X`, where
`X` has only its first row nonzero and `X^2 = 0`. So `U^2 = I + 2X`.
Conjugating by `D = diag(1,2,2)` scales entry `(i,j)` by `d_j/d_i`, which
gives `M2^(-1) U M2 = [[1,4,2],[0,1,0],[0,0,1]] = U^2`.

**Separation and survival.**

* `rho(v) = M2 U M2^(-1) = [[1,1,1/2],[0,1,0],[0,0,1]]` is non-integral.
  But `M0` and `M1` lie in `GL_3(Z)`, since they are integral with
  determinant 1. So `rho(v)` is not in `rho(F_-)`.
* `rho(u) = U ≠ I`.
* `rho(b_1) = [[1,0,2],[0,1,0],[0,0,1]] ≠ I`.

**Solvability.** `L = <M0,M1,M2>` is upper triangular in `GL_3(Z[1/2])`,
hence solvable of length at most 3. The configuration is finitely
supported, so D gives `pi : G_2 -> L wr Z`. Its derived length is at most 4,
and at least 3 by C. It keeps `u` and `b_1` and separates `v` from `F_-`.

**Machine checks.**

* `verify_wreath.py` recomputes all of this in exact rational arithmetic.
  It evaluates the relator of `G_2` in `L wr Z` directly and confirms it is
  the identity. The output is in `verify_wreath.out`.
* `search_window.py` enumerates small integer upper-triangular windows and
  finds 576 configurations with the same properties (`search_window.out`).
* `lis.g` runs GAP `LowIndexSubgroupsFpGroup(G_2, 8)`. It finds 253
  subgroups; `u` survives in 53 images and `b_1` survives in all 53. In
  none of them is `v` outside `<pi(a_0), pi(a_1)>` (`vsep = 0`), as B
  requires. The images include `S_3`, `PSL(3,2)`, `PGL(2,7)`, `A_7`, `S_7`,
  `A_8` and `S_8` (`lis.out`).

`[machine-checked]`
