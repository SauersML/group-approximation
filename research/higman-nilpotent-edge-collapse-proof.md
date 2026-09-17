---
rg: 2
id: higman-nilpotent-edge-collapse-proof
kind: route
title: One conjugation by a power of b scales the a-conjugates of c by distinct exponents, which a nilpotent group of finite Hirsch length cannot host
target: nilpotent-edge-images-collapse-higman-quotients
requires:
  - nontrivial-higman-quotients-keep-all-four-bs-subgroups
artifacts:
  - experiments/higman-edge-collapse-2026-09-17/README.md
---

Conventions: `x^y = y^-1 x y` and `[x,y] = x^-1 y^-1 x y`. Let `Q = H4/R` with `Q != 1`. We derive a
contradiction from each hypothesis. Throughout we write `a, b, c, d` for the images in `Q`. By item 1
of `nontrivial-higman-quotients-keep-all-four-bs-subgroups`, they have infinite order.

## Item 1

**Step 1 (the identity `b^m a^k = a^k b^(2^k m)`).** From `a^-1 b a = b^2` we get `b a = a b^2`, and then
`b^m a = a b^(2m)` by induction on `m`. Induction on `k` gives
`b^m a^(k+1) = (b^m a^k) a = a^k b^(2^k m) a = a^(k+1) b^(2^(k+1) m)`.

**Step 2 (eigen-relations).** Put `u_k = a^-k c a^k` for `k >= 0`. By Step 1 with `m = 1`,
`a^k b^(2^k) = b a^k`. Hence

```text
u_k^(b^(2^k)) = (a^k b^(2^k))^-1 c (a^k b^(2^k)) = (b a^k)^-1 c (b a^k) = a^-k (b^-1 c b) a^k = a^-k c^2 a^k = u_k^2.
```

Iterating `2^(K-k)` times, for all `0 <= k <= K` with `g_K = b^(2^K)`:

```text
g_K^-1 u_k g_K = u_k^(n_k),   n_k = 2^(2^(K-k)).
```

The exponents `n_0 > n_1 > ... > n_K = 2` are distinct. Each `u_k` is conjugate to `c`, so it has
infinite order.

**Step 3 (pass to a nilpotent group).** Suppose all `u_k` lie in a finitely generated virtually nilpotent
subgroup `N` of `Q`. This holds in particular with `N = <a,c>` when the image of `<a,c>` is virtually
nilpotent.
- Let `N_0` be a normal nilpotent subgroup of finite index `m` in `N`. It is finitely generated, so it
  has a finite Hirsch length `h`.
- Put `v_k = u_k^m`. Since `N/N_0` has order `m`, `v_k` lies in `N_0`, and it has infinite order.
- Because `u_k^(g_K) = u_k^(n_k)`, also `v_k^(g_K) = v_k^(n_k)`.

**Step 4 (a self-map of a finitely generated nilpotent group).** Fix `K = h`. Let `M = <v_0, ..., v_K>`
be the subgroup of `N_0`. It is finitely generated nilpotent with Hirsch length `h(M) <= h`.
- Conjugation by `g_K` is an automorphism of `Q`. It sends each generator `v_k` of `M` to
  `v_k^(n_k)`, which lies in `M`. So it restricts to a homomorphism `phi : M -> M`.
- The torsion elements of `M` form a finite normal subgroup `T`, and `phi(T) <= T`. So `phi` induces
  an endomorphism `phibar` of the torsion-free finitely generated nilpotent group `P = M/T`.
- `h(P) = h(M) <= h`.
- The images `vbar_k` of `v_k` in `P` are nontrivial, because `v_k` has infinite order.

**Step 5 (Mal'cev linearisation).** By Mal'cev's theory (e.g. Segal, *Polycyclic groups*, Ch. 6):
- `P` embeds in its rational completion `P_Q`.
- There is a nilpotent Lie algebra `p` over `Q` with `dim_Q p = h(P)` and a bijection
  `log : P_Q -> p` such that `log(x^n) = n log x` for all `n` in `Z`.
- Every endomorphism of `P` extends uniquely to `P_Q`, and `log` conjugates it to a `Q`-linear Lie
  algebra endomorphism `L` of `p`.

Applying this to `phibar`:

```text
L(log vbar_k) = log(phibar(vbar_k)) = log(vbar_k^(n_k)) = n_k log vbar_k,   log vbar_k != 0.
```

So `log vbar_0, ..., log vbar_K` are eigenvectors of the linear map `L` with pairwise distinct
eigenvalues `n_0, ..., n_K`. They are therefore linearly independent, and
`K + 1 <= dim p = h(P) <= h = K`. This is a contradiction, so `Q = 1`.

**The pair `<b,d>`.** The map `theta : a -> b -> c -> d -> a` is an automorphism of `H4`, since it permutes
the four relators cyclically. If `Q = H4/R`, then `theta` induces an isomorphism `H4/theta^-1(R) -> Q` that
sends the images of `a, c` to the images of `b, d`. So if `<b,d>` has virtually nilpotent image in `Q`, then
`<a,c>` has virtually nilpotent image in `H4/theta^-1(R)`. That group is trivial by the above, and hence
so is `Q`.

## Item 1, solvable version (finite Hirsch length)

The Mal'cev step can be replaced by linear algebra on the factors of the derived series. This removes
nilpotency and keeps only finite rank.

**Setting.** Suppose all `u_k` lie in a subgroup `N` of `Q` that has a normal solvable subgroup `N_0` of
finite index `m`, of finite Hirsch length (torsion-free rank) `h`. Here
`h(S) = sum_i dim_Q (S^(i)/S^(i+1) ⊗ Q)` over the derived series of a solvable group `S`.
- This rank is additive along any subnormal series with abelian factors.
- It does not increase on passing to subgroups (Lennox--Robinson, *The theory of infinite soluble
  groups*, §1.3).

Examples:
- every virtually polycyclic group;
- `BS(1,n)`.

**Step 3'.** As in Step 3, `v_k = u_k^m` lies in `N_0`, has infinite order, and satisfies
`v_k^(g_K) = v_k^(n_k)`. Fix `K = h`, let `M = <v_0, ..., v_K> <= N_0`, and let `phi : M -> M` be conjugation
by `g_K`, as in Step 4. Then `h(M) <= h`.

**Step 4'.** Every homomorphism maps derived subgroups into derived subgroups. So `phi(M^(i)) <= M^(i)`,
and `phi` induces `Q`-linear maps `L_i` on the finite-dimensional spaces `V_i = (M^(i)/M^(i+1)) ⊗ Q`.

**Step 5'.** For each `k`:
- Let `i(k)` be the largest `i` such that some positive power `v_k^(r_k)` lies in `M^(i)`. It exists,
  because `M^(0) = M` and `M^(l) = 1` for the derived length `l`, while `v_k` has infinite order.
- The image `w_k` of `v_k^(r_k)` in `V_(i(k))` is nonzero. Otherwise a further power of `v_k^(r_k)`
  would lie in `M^(i(k)+1)`, contradicting the maximality of `i(k)`.
- `L_(i(k))(w_k) = n_k w_k`.

For a fixed `i`, the vectors `w_k` with `i(k) = i` are eigenvectors of `L_i` with pairwise distinct
eigenvalues, so they are linearly independent. Summing over `i`:

```text
K + 1 <= sum_i dim V_i = h(M) <= h = K,
```

which is a contradiction. So `Q = 1` whenever the image of `<a,c>` (or, via `theta`, of `<b,d>`) is
virtually solvable of finite Hirsch length. Item 3 extends in the same way: a nontrivial quotient acting
on a tree without inversions, with all edge stabilizers virtually solvable of finite Hirsch length, fixes
a vertex.

**Calibration.**
- For the analogue of `H4` with `BS(1,m)` replaced by `Z^2` (all exponents 1), the eigenvalues coincide
  and the argument rightly says nothing, since `Z^4` is a nontrivial quotient.
- For the base-3 analogue `< a,b,c,d | b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3 >`, the abelianization
  is `(Z/2)^4`. It is a nontrivial finite quotient in which `<a,c>` has the finite image `(Z/2)^2`. There
  `c` has order 2, so the infinite-order input fails and the argument rightly says nothing.
- Steps 1–5 work verbatim for the base-`p` analogue, `p >= 2`, with exponents `p^(p^(K-k))`, provided
  the generators have infinite order. Glebsky's sofic quotients of the base-`p` group for `p >= 3`, into
  which `BS(1,p)` embeds (Kassabov--Kuperberg--Riley, arXiv:1712.07191, l.274 of the TeX), satisfy that
  input. There the argument says only that `<a,c>` has an image of infinite Hirsch length. This is
  consistent, since those quotients contain `BS(1,p)` and are not virtually nilpotent.
- The only place `H4` is special is item 1 of `nontrivial-higman-quotients-keep-all-four-bs-subgroups`.

## Item 2 (tree gate)

Let `Q` act on a tree `X` without inversions. Write `Fix(g)` for the fixed subtree of `g`.

**Step 6 (generators are elliptic).** Translation length satisfies `l(g^n) = |n| l(g)` and is a conjugacy
invariant. Each generator `g` is conjugate to `g^2`, so `l(g) = 2 l(g)` and `l(g) = 0`. Without
inversions, `l(g) = 0` means `g` fixes a vertex.

**Step 7 (cyclically adjacent generators have a common fixed point).** Let `(x, y)` be one of
`(a,b), (b,c), (c,d), (d,a)`, so `x^-1 y x = y^2`. Put `Y = Fix(y)`. Then

```text
x^-1 Y = Fix(x^-1 y x) = Fix(y^2) ⊇ Y.
```

Suppose `F = Fix(x)` is disjoint from `Y`.
- Let `[p,q]` be the bridge from `F` to `Y`, with `p` in `F`, `q` in `Y` and `p != q`. Every path from a
  point of `Y` to `F` passes through `p`.
- The first edge `e` of `[p,q]` is not fixed by `x`, since otherwise `F` would contain it.
- `x^-1 Y` is a subtree whose bridge to `F` starts with the edge `x^-1 e != e` at `p`.
- So a geodesic from a point of `Y` to a point of `x^-1 Y` passes through `p`, which lies in neither
  subtree. Hence `Y ∩ x^-1 Y = ∅`.

This contradicts `x^-1 Y ⊇ Y != ∅` (Step 6). So `Fix(x) ∩ Fix(y) != ∅`.

**Step 8 (Helly).** Subtrees of a tree satisfy the Helly property: pairwise intersecting finite families
have a common point.
- If `Fix(a) ∩ Fix(c) != ∅` and `Fix(b) ∩ Fix(d) != ∅`, then by Step 7 the four fixed subtrees
  pairwise intersect. So `a, b, c, d`, and hence `Q`, fix a common vertex.
- Otherwise, say `Fix(a) ∩ Fix(c) = ∅`. Let `[p,q]` be the bridge, with `p` in `Fix(a)`, `q` in
  `Fix(c)` and at least one edge. By Step 7, `Fix(b)` meets both `Fix(a)` and `Fix(c)`. So it contains a
  geodesic from `Fix(a)` to `Fix(c)`, and every such geodesic contains the bridge. The same holds for
  `Fix(d)`. So `b` and `d` fix every edge of `[p,q]`.
- Symmetrically, if `Fix(b) ∩ Fix(d) = ∅`, then `a` and `c` fix an edge.

## Item 3

Suppose `Q != 1` fixes no vertex. By Item 2, some edge stabilizer contains `<a,c>` or `<b,d>`. A subgroup
of a virtually nilpotent group is virtually nilpotent (and finite Hirsch length passes to subgroups), so Item 1 gives `Q = 1`, a contradiction. A
nontrivial splitting as an amalgam or HNN extension gives a Bass--Serre tree action without inversions
and without a global fixed point, with edge stabilizers conjugate to the edge group. So such a splitting
of a nontrivial `Q` over a virtually nilpotent group is impossible.
