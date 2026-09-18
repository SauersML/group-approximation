---
rg: 2
id: cone-diagonal-roots-miss-a-kl-word-over-thompson-v-proof
kind: route
title: The census S_3 = <a,c> permutes three cones rigidly, cone-diagonal endomorphisms keep its orbits of size one or three, and the Sym(Omega) obstruction applies
target: cone-diagonal-roots-miss-a-kl-word-over-thompson-v
requires: [cantor-homeomorphisms-miss-a-unimodular-root, kl-failure-localizes-to-the-coefficient-subgroup, kervaire-laudenbach-holds-for-hyperlinear]
---

Right action throughout: `x y` means first `x`, then `y`, as in
`experiments/kl-thompson-v-census/vgroup.py`.

## Step 1: `F = <a, c>` is `S_3`, and `a, c` are distinct transpositions

- `a = (00 01)` sends `00z <-> 01z` and fixes `1z`.
- `c = (1 00)` sends `1z <-> 00z` and fixes `01z`.

Both are involutions. `ac` sends `00z -> 01z -> 01z`, `01z -> 00z -> 1z` and
`1z -> 1z -> 00z`, so it cycles `00 -> 01 -> 1` and has order `3`.

So `F` acts on the three prefixes `{00, 01, 1}` through `S_3`, and `a`, `c`
act as two distinct transpositions. The action is faithful, since `z` is
carried along unchanged. Hence `F ≅ S_3`, of order `6`. This agrees with the
census computation "`<a,c>` (order 6)" in
`research/artifacts/kl-thompson-v-generator-census-2026-09-13.md`, and with
the check in `research/artifacts/kl-thompson-v-internal-roots-2026-09-17.md`.

## Step 2: every `F`-orbit on `C` has size exactly `3`

Every point of `C` is `p z` with `p in {00, 01, 1}`. By Step 1, `F` moves `p`
through all three prefixes and leaves `z` unchanged. So the orbit is
`{00z, 01z, 1z}`, of size `3`.

## Step 3: cone-diagonal endomorphisms keep the orbit type `{1, 3}`

**`phi(g)` is in `V`.** Take `phi` as in the claim. On `U_i`, `phi(g)` is
`h_i^(-1) g h_i`. Refine a tree pair of `g` to the codes on which `h_i^(-1)`
and `h_i` act as prefix replacements, and compose. Then `phi(g)|U_i` is a
prefix replacement between complete prefix codes of `U_i`. On `R` it is the
identity. So `phi(g) in V`.

**`phi` is an injective homomorphism.** It is a homomorphism piece by piece.
If `g != 1` moves `z`, then `phi(g)` moves `z h_1`, so `phi` is injective.

**The orbits.**
- For `y in U_i`, the `phi(F)`-orbit of `y` is the image under `h_i` of the
  `F`-orbit of `y h_i^(-1)`, so it has size `3` by Step 2.
- For `y in R`, the orbit is `{y}`.
- `U_1` is nonempty, so some orbit has size `3`.

Since `phi` is injective, `phi(a)` and `phi(c)` are distinct transpositions
generating `phi(F) ≅ S_3`.

## Step 4: no root in `Sym(C)`

**Rewriting the relation.** Suppose `x in Sym(C)` satisfies
`phi(c) x phi(a) x phi(a) x^(-1) = 1`. Conjugating by `phi(c)` gives

    x a' x a' x^(-1) b' = 1,     a' = phi(a),  b' = phi(c).

**Applying the import.** Import `cantor-homeomorphisms-miss-a-unimodular-root`,
item 2, verbatim:

> For any set `Omega` with an action of `S_3 = <a, b>` whose orbits all have
> size `1` or `3`, with at least one of size `3`, there is no
> `x in Sym(Omega)` with `x a x a x^(-1) b = 1`.

Apply it with `Omega = C`, `S_3 = <a', b'>` and the orbit type of Step 3.
Then no such `x` exists.

**The composition convention does not matter.**
- Reading a relation in the opposite composition order reverses it.
- The reverse of `x a' x a' x^(-1) b'` is `b' x^(-1) a' x a' x`.
- Its inverse is `x^(-1) a' x^(-1) a' x b'`, because `a'` and `b'` are
  involutions.
- With `y = x^(-1)`, that is `y a' y a' y^(-1) b'`.

So a root exists under one convention iff one exists under the other.

Hence `w0^phi` has no root in `Sym(C)`, and so none in `Homeo(C)` or in `V`.
This is item 2 of the claim.

## Step 5: Kervaire--Laudenbach holds for `w0`

**Localization.** The coefficients of `w0` are `c, a, a`, which lie in the
finite group `F`. Import `kl-failure-localizes-to-the-coefficient-subgroup`,
verbatim:

> If `A -> A_w` is injective then `G -> G_w` is injective.

It applies with `G = V` and `A = F`.

**`F` is hyperlinear.** The definition quoted in
`kervaire-laudenbach-holds-for-hyperlinear` is "a group which can be
embedded into a certain metric ultraproduct of unitary groups". A finite
group embeds in `U(6)` by its regular representation, hence diagonally in
that ultraproduct.

**The conjecture for `F`.** The same node quotes Nitsche--Thom Theorem 1.2:

> This proves the original Kervaire--Laudenbach Conjecture for
> Connes-embeddable groups.

- `deg_t(w0) = 1`, so `epsilon(w0) = t`.
- The presentation complex of `<t | t>` is contractible, so its second
  homology is trivial.
- So `F -> F_w0` is injective.

By localization, `V -> V_w0` is injective. This is item 1 of the claim.
