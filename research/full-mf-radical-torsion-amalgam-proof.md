---
rg: 2
id: full-mf-radical-torsion-amalgam-proof
kind: route
title: Amalgamate two cyclic permutation extensions along an infinite-order element so the orders two and three collide at one
target: full-mf-radical-seed-has-no-torsion-free-quotient
requires:
  - universal-mf-quotient
  - full-mf-radical-forces-perfect-commutator-bound
  - full-mf-radical-has-fp-cover-same-generators
  - torsion-free-universal-quotient-recursively-presented
artifacts:
  - research/artifacts/homomorphic-image-transfer-obstruction-2026-09-08.md
---

Write `Z_MF = {G countable : Rad_MF(G) = G}`, the class of
`full-mf-radical-groups-form-an-extension-colimit-class`; by
`universal-mf-quotient` membership says exactly that every homomorphism to a
countable MF group is trivial.

Two steps below are clauses of existing nodes -- the free-product closure of
`Z_MF` is clause 4 of `full-mf-radical-groups-form-an-extension-colimit-class`,
and the torsion-free vanishing is clause 1 of
`torsion-generated-mf-absorbers-die-in-torsion-free-targets`.  Both are proved
inline instead of required, because each is two lines here while those nodes
carry chains this region has no other use for.

## 0. Normalizing the input

`H` is nontrivial, finitely generated and in `Z_MF`.  Two reductions come from
prerequisites rather than from a new argument.

By `full-mf-radical-has-fp-cover-same-generators` there is a **finitely
presented** group on the same generating set with full MF radical, surjecting
onto `H`; it is nontrivial because it surjects onto a nontrivial group.
Replace `H` by it.

By `full-mf-radical-forces-perfect-commutator-bound`, `H` is **perfect**.
(Directly: a nontrivial finitely generated abelianization has a nontrivial
finite cyclic quotient, and finite groups are MF.)

## 1. The base

Put `B = H * H`.  Then:

- `B` is finitely presented, being a free product of two finitely presented
  groups;
- `B` is perfect, since the abelianization of a free product is the direct sum
  of the abelianizations;
- `B` lies in `Z_MF`.  Directly: a homomorphism `B -> M` with `M` MF restricts
  to each free factor, and both restrictions are trivial because `H in Z_MF`
  and the image is a countable subgroup of `M`, hence a countable MF group; the
  universal property of the free product then makes the whole map trivial.

Choose `h != 1` in `H` and let `a in B` be the product of the copy of `h` in
the first free factor with the copy in the second.  For `n >= 1`, `a^n` is a
reduced alternating word of length `2n` in the free product, so `a^n != 1`:
`a` has infinite order.

## 2. Two cyclic permutation extensions

For `m = 2, 3` let `C_m = <t_m | t_m^m = 1>` act on `B^m` by cyclic coordinate
permutation and put

```text
W_m = B^m x| C_m,       u_m = (a,1,...,1) t_m.
```

`W_m` is finitely presented: take a presentation of `B` in each coordinate,
commutation relations between distinct coordinates, `t_m^m = 1`, and the
conjugation relations implementing the permutation.

Conjugating the coordinate tuple by successive powers of `t_m` and using
`t_m^m = 1`,

```text
u_m^m = (a, a, ..., a),
```

which has infinite order because `a` does.  So `u_m` has infinite order and
`<u_m>` is infinite cyclic.

**Every MF-valued homomorphism kills the base.**  If `phi : W_m -> M` with `M`
MF, then for each coordinate copy of `B` the image `phi(B)` is a countable
subgroup of an MF group, hence a countable MF group, so `phi|_B` is trivial
because `B in Z_MF`.  Hence `phi` factors through `C_m`, and in particular

```text
phi(u_m) = phi(t_m).                                                  (HIT4)
```

**`t_m` normally generates `W_m`.**  In `W_m/<<t_m>>` the relation `t_m = 1`
identifies the `m` coordinate copies of `B`, since `t_m` conjugates coordinate
`i` onto coordinate `i+1`.  Distinct coordinates commute elementwise in `W_m`,
so their common image commutes with itself: it is abelian.  It is also a
quotient of the perfect group `B`, hence perfect, hence trivial.  With the
base gone and `t_m = 1`, the quotient is trivial, so `W_m = <<t_m>>`.  This is
where `m >= 2` and perfectness of `B` are both used.

## 3. The amalgam

Define

```text
K = W_2 *_(<u_2> = <u_3>) W_3,
```

amalgamating the two infinite cyclic subgroups by `u_2 -> u_3`.  It is
finitely presented, being an amalgam of finitely presented groups over a
finitely generated subgroup.

**Both factors embed.**  This is the normal form for amalgamated free
products.  An elementary substitute, which avoids importing that theorem: let
`W_m` act on `Omega_m = W_m x N` by left multiplication on the first
coordinate.  The action is faithful, and since `u_m` has infinite order, the
orbits of `<u_m>` are the right cosets `<u_m> w`, each infinite, and there are
countably infinitely many of them.  So there is a bijection
`Omega_m -> Z x N` carrying the action of `u_m` to `(k,n) -> (k+1,n)`
(enumerate the orbits, pick a base point in each, use the `u_m`-exponent as
the first coordinate).  Transport both actions to `Z x N`.  The two
transported permutations representing `u_2` and `u_3` are equal, so the
universal property of the amalgam gives `K -> Sym(Z x N)` restricting to the
two faithful actions.  Hence `W_2` and `W_3` inject into `K`; in particular
`K != 1` and `t_2, t_3` retain orders exactly `2` and `3`.

## 4. `(HIT1)`: full MF radical

Let `phi : K -> M` with `M` MF.  Applying `(HIT4)` on each side and the
amalgamating relation,

```text
phi(t_2) = phi(u_2) = phi(u_3) = phi(t_3) =: g.
```

Then `g^2 = 1` from `t_2^2 = 1` and `g^3 = 1` from `t_3^3 = 1`, so
`g = g^3 (g^2)^-1 = 1`.  Hence `phi` kills `t_2` and `t_3`, and it already
kills both bases, so it kills `W_2` and `W_3`, which generate `K`.  So `phi`
is trivial and `Rad_MF(K) = K`.

## 5. `(HIT2)` and `(HIT3)`: torsion normal generation and its consequences

By step 2 each `W_m = <<t_m>>_(W_m)`, so `K = <<t_2, t_3>>_K`.  That is
`(HIT2)`.

Let `q : K ->> Q` be nontrivial.  If `q(t_2) = q(t_3) = 1` then `q` kills
`<<t_2,t_3>> = K` and `Q = 1`.  So `q(t_2) != 1` or `q(t_3) != 1`, and the
order of that image divides `2` respectively `3` and exceeds `1`, hence is
exactly `2` or exactly `3`.

Because `K` is normally generated by two torsion elements it is generated by
their conjugates, all of which are torsion.  Let `f : K -> T` with `T`
torsion-free.  Each generator has finite order, so its image has finite order,
so its image is `1`.  Hence `f` is trivial.  (This is clause 1 of
`torsion-generated-mf-absorbers-die-in-torsion-free-targets`, reproved in place
so that this region does not inherit that node's Leavitt prerequisites.)  By
the universal property in
`torsion-free-universal-quotient-recursively-presented`, that says exactly
`K^tf = 1`, which is `(HIT3)`.

## 6. The obstruction

`K` satisfies the hypothesis it was built from, so a procedure claimed to work
on every full-MF-radical input must work on `K`.  Any such procedure returning
a homomorphic image of its input returns a quotient of `K`, and by step 5 every
nontrivial quotient of `K` has an element of order `2` or `3`.  So no such
procedure returns a nontrivial torsion-free group on every input.

Nothing here constrains a torsion-free group mapping **onto** `K`; free groups
already do that.
