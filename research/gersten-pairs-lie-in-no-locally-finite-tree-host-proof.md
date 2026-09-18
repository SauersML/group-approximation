---
rg: 2
id: gersten-pairs-lie-in-no-locally-finite-tree-host-proof
kind: route
title: The base is elliptic, the prime support of local orders is a conjugacy invariant, and squaring by a conjugate of a kills the smallest prime
target: gersten-pairs-lie-in-no-locally-finite-tree-host
requires:
  - baumslag-gersten-base-is-elliptic-in-every-tree-action
  - baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman
---

Throughout, `(a, t)` is a Gersten pair in `Γ`, `b = t a t^-1`, and
`B = <a, b>`. The assignment `a -> a`, `t -> t` defines a homomorphism
`BG -> Γ`, since the one relator of `BG` holds in `Γ`. So every action of `Γ` on
a tree is also an action of `BG`.

## Step 0: reduction to a common fixed vertex

Let `Γ` act on a locally finite tree `T`. Let `T'` be its barycentric
subdivision. `Γ` acts on `T'` without inversions, `T'` is locally finite, and
the kernel is unchanged. By `baumslag-gersten-base-is-elliptic-in-every-tree-action`,
item 1 (which uses only the relations of `BG`, so it applies to the action
pulled back along `BG -> Γ`), `B` fixes a vertex `w` of `T'`.

## Step 1: local orders

For an element `x` fixing a vertex `u` of `T'` and `R >= 0`, the ball
`B_R(u)` is finite and `x`-invariant. Let `o_u(x, R)` be the order of the
permutation `x` induces on it. Let `P_u(x)` be the set of primes dividing
`o_u(x, R)` for some `R`.

- **(L1) Independence of the vertex.** If `x` fixes `u` and `u'` with
  `d(u, u') = D`, then `B_R(u) ⊆ B_(R+D)(u')`, both invariant. The order of a
  permutation restricted to an invariant subset divides the order on the larger
  set. So `o_u(x, R)` divides `o_(u')(x, R+D)`, and symmetrically. Hence
  `P_u(x) = P_(u')(x)`.
- **(L2) Conjugation.** For `g in Γ`, `g` maps `B_R(u)` bijectively onto
  `B_R(gu)` and intertwines `x` with `g x g^-1`. So
  `o_(gu)(g x g^-1, R) = o_u(x, R)` and `P_(gu)(g x g^-1) = P_u(x)`.

`a` fixes `w`, so `b = t a t^-1` fixes `tw`, and `b` fixes `w` because `B` does.
By (L2) and (L1), `P_w(b) = P_(tw)(b) = P_w(a)`. Call this set `P`.

## Step 2: the smallest prime

Suppose `a` acts nontrivially on `T'`, moving some vertex `u`. For
`R >= d(w, u)` the permutation `α` induced by `a` on `B_R(w)` is nontrivial, so
`P` is nonempty. Let `p = min P`, and choose `R` with `p | m := o_w(a, R)`. Let
`β` be the permutation induced by `b` on `B_R(w)`, and `ℓ = o_w(b, R)`.

1. `β α β^-1 = α^2`, so `α^2` is conjugate to `α` and has the same order `m`.
   Hence `m` is odd, and `p >= 3`.
2. By induction `β^k α β^-k = α^(2^k)`. With `k = ℓ`, `β^ℓ = 1` gives
   `α = α^(2^ℓ)`, so `2^ℓ ≡ 1 (mod m)` and in particular `(mod p)`.
3. Let `d = ord_p(2)`. Then `d | ℓ` and `d | p - 1`. Since `p >= 3`,
   `2 ≢ 1 (mod p)`, so `d >= 2`.
4. Let `q` be a prime factor of `d`. Then `q <= d <= p - 1 < p`, and `q | ℓ`,
   so `q in P_w(b) = P`. This contradicts `p = min P`.

So `a` acts trivially on `T'`, hence on `T`.

## Step 3: items 1 and 2

- **Item 1.** `a` lies in the kernel, which is torsion, but `a` has infinite
  order. Contradiction.
- **Item 2.** Apply Steps 0--2 to each `T_i` separately. `a` acts trivially on
  every `T_i`, so it lies in the common kernel, which is torsion. Contradiction.

## Step 4: item 3

- **(E1)** is item 1 with trivial kernel, applied to the subgroup `Γ` of the host,
  whose restricted action is faithful.
- **(E2)** The Bass--Serre tree of a finite graph of groups is locally finite
  when every edge group has finite index in its vertex groups: the valence at a
  vertex with group `G_v` is the sum over incident edges `e` of
  `[G_v : G_e]` (Serre, *Trees*, §I.5). Faithfulness then reduces to (E1).
- **(E3)** A locally finite rooted tree is a locally finite tree, and its
  automorphism group acts faithfully.
- **(E4')** is item 2.

A subgroup of a host acts on the same trees with a kernel contained in the
host's kernel, so the hypotheses pass to subgroups.

## Step 5: item 4

- `BS(1,2)` embeds in a finitely presented simple group by
  `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`.
- `x -> x+1` and `x -> 2x` satisfy `b a b^-1 = (x -> x+2) = a^2`, and they
  generate `Z[1/2] ⋊ <2>`, which is a faithful image of `BS(1,2)` (the classical
  identification `BS(1,2) ≅ Z[1/2] ⋊ Z`). A word in `a, b` evaluates to an
  affine map `x -> 2^k x + r` with `k in Z` and `r in Z[1/2]`, computed exactly.
  It lies in `<a>` iff `k = 0` and `r in Z`, and in `<b>` iff `r = 0`. So both
  memberships are decidable.
- `A*_phi = < a, b, t | b a b^-1 = a^2, t a t^-1 = b >`. Eliminating `b` gives
  the presentation of `BG`. In it `a` has infinite order, because `A` embeds in
  the HNN extension. So `(a, t)` is a Gersten pair, and item 3 applies.
- For a general input, an `a in C_1` of infinite order with
  `phi(a) a phi(a)^-1 = a^2` gives the Gersten pair `(a, t)` in `A*_phi`, since
  `t a t^-1 = phi(a)`.
- The input is a Magnus step: `BG` is the HNN extension of the one-relator group
  `BS(1,2)` along the Magnus subgroups `<a_0>` and `<a_1>` (see
  `baumslag-gersten-base-is-elliptic-in-every-tree-action`).

QED
