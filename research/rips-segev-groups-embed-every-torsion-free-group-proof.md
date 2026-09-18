---
rg: 2
id: rips-segev-groups-embed-every-torsion-free-group-proof
kind: route
title: Rips--Segev relators only see a and b, so the group over H * Z is H amalgamated with the core group over <a>
target: rips-segev-groups-embed-every-torsion-free-group
requires:
  - kaplansky-three-properties-fixed-fp-torsion-free-tester
  - rips-segev-witness-supports-carry-no-zero-divisors
---

**Conventions.**  Everything follows Steenbock, arXiv:1307.0981 (TeX source read 2026-09-17).
- `|.|_*` is free product length.
- `Lambda` is the maximal piece length and `gamma` the minimal cycle length, both over reduced equivalent graphs.
- `Gr'_*(lambda)` means `Lambda / gamma < lambda`.

The citations are:
- Proposition "criterion": if `(|omega(p)|_* + 2) / |omega(c)|_* < lambda` for all pieces `p` and non-trivial cycles
  `c` of `Omega` itself, then `Gr'_*(lambda)` holds.  It is stated and proved for an arbitrary free product `F`.
- Lemma "maxplength": pieces of a generalized Rips--Segev graph under the Rips--Segev condition have
  `|omega(p)|_* <= 3`.
- Lemma "mincycle": `gamma(Gamma) >= girth(Phi_Gamma)`.
- Corollary "final graphical small cancellation for Rips-Segev": Rips--Segev condition plus girth 41 gives
  `Gr'_*(1/8)`.  Explicit constructions: Steenbock's table satisfies the Rips--Segev condition, and underlying
  graphs of arbitrarily large girth exist.
- Theorem "tf": `Gr'_*(1/8)` over finitely generated torsion-free factors gives a torsion-free group.
- Theorem "lii": `Gr'_*(1/6)` gives a linear isoperimetric inequality, and a hyperbolic group when the factors are
  hyperbolic and `Omega` is finite.
- Proposition "small cancellation on RSgraphs": under `Gr'_*(1/6)`, `A` and `B` embed and have no unique product.

## Step 0.  The small-cancellation data of `Gamma` do not depend on the factors

Let `G_1, G_2` be torsion-free with `1 != a in G_1` and `1 != b in G_2`.  Since `a` and `b` have infinite order, the
normal form theorem for free products makes `<a, b> <= G_1 * G_2` free on `a, b`.  So:
- For words `u, v` in `a^{+-1}, b^{+-1}`, `u = v` in `F` if and only if `u = v` in `F_2 = <a> * <b>`.
- `|u|_*` in `F` equals the syllable length of `u` in `F_2`.

Every path label of `Gamma` is such a word.  So the following notions are the same over `G_1 * G_2` and over `F_2`:
- the reducedness of the labelling;
- the set of pieces of `Gamma` and their lengths;
- the free product lengths of cycles of `Gamma`.

This is Steenbock's "Case 2" remark: "the elements `a` and `b` generate a free subgroup of `G_1*G_2`.  Thus, Case 2
is a generalization of Case 1".

Take Steenbock's table and `girth(Phi) >= 41`.  Then `|omega(p)|_* <= 3` for pieces, and `|omega(c)|_* >= 41` for
non-trivial cycles.  The criterion gives `Gr'_*(1/8)` because `5/41 < 1/8`.  This holds over every `G_1 * G_2`
simultaneously, and in particular over `F_2`.  So:
- `K_Gamma = F_2 / <<R>>` is torsion-free (Theorem "tf" with factors `Z, Z`).
- `A` and `B = {1, a, b, ab}` embed in `K_Gamma` and have no unique product there.  In particular `a != 1` and
  `b != 1` in `K_Gamma`, so both have infinite order in `K_Gamma`.
- The elements `c_i` are labels of paths of `Gamma`, hence words in `a, b`.  So `A` and `B` lie in the image of
  `F_2`, which is `K_Gamma`.

## Step 1.  Amalgam decomposition

Let `P = <G_1, G_2 | R(a, b)>`, which is `G(Gamma)`.  Let `Q = G_1 *_{<a>} K_Gamma *_{<b>} G_2`, where the edge
maps send `a in G_1` to `a in K_Gamma` and `b in G_2` to `b in K_Gamma`.  Both edge maps are injective by Step 0 and
torsion-freeness.

A presentation of `Q` is obtained as follows.
- Start from `G_1 * K_Gamma * G_2`, where `K_Gamma = <a', b' | R(a', b')>`.
- Add the relations `a' = a` and `b' = b`.
- A Tietze move eliminates `a'` and `b'`.

What remains is `<G_1, G_2 | R(a, b)>`, which is `P`.  So `G(Gamma) = Q`.

With `G_1 = H` and `G_2 = <b> = Z`, the second amalgamation is trivial, since `<b>` is all of `G_2`.  So
`G(Gamma) = H *_{<a>} K_Gamma`.

## Step 2.  Embedding, torsion, unique products, finiteness

- **Embedding.**  By the normal form theorem for amalgamated free products, both vertex groups embed.  So `H` and
  `K_Gamma` embed in `G(Gamma)`.
- **Torsion.**  A finite-order element of an amalgam is conjugate into a vertex group.  `H` and `K_Gamma` are
  torsion-free, so `G(Gamma)` is torsion-free.  Theorem "tf" gives the same conclusion directly, using Step 0 over
  the finitely generated torsion-free factors `H, Z`.
- **No unique products.**  `(A, B)` has no unique product in `K_Gamma` (Step 0).  `K_Gamma` embeds, so it has none
  in `G(Gamma)`.  This is also Steenbock's proposition directly.
- **Hyperbolicity.**  If `H` is hyperbolic, the factors `H, Z` are hyperbolic, `Gamma` is finite, and Step 0 gives
  `Gr'_*(1/8)` over `H * Z`.  Theorem "lii" then makes `G(Gamma)` hyperbolic.
- **Finite presentation.**  If `H` is finitely presented, then `G(Gamma) = <H, b | R>`.  This has finitely many
  relators beyond those of `H`, since a finite `Gamma` has a finite generating set of cycles.  So it is finitely
  presented.

If `H = 1`, replace `H` by `Z`; the conclusions about subgroups of `H` are unaffected.  This proves the theorem.

## Step 3.  (E1), (E1'), (E2)

**(E1).**  The forward direction holds because every generalized Rips--Segev group in the setting is torsion-free
(Theorem "tf").

For the converse, suppose `alpha beta = 0` with `alpha, beta != 0` in `k[G]`, `G` torsion-free.
- Let `H = <supp alpha, supp beta>`.  It is finitely generated and torsion-free, and `alpha, beta in k[H]`.
- `H != 1`, because `k` is a field.
- Choose `1 != a in H` and form `G(Gamma) = H *_{<a>} K_Gamma`.
- The injective homomorphism `H -> G(Gamma)` induces an injective ring homomorphism `k[H] -> k[G(Gamma)]`.  So
  `k[G(Gamma)]` has a zero-divisor pair.

**(E1').**
- `U` is finitely presented and torsion-free (`kaplansky-three-properties-fixed-fp-torsion-free-tester`), and
  `U != 1`.
- By Step 2, `G_U = U *_{<a>} K_Gamma` is finitely presented, torsion-free and without unique products.
- If `k[G_U]` is a domain, then `k[U] <= k[G_U]` is a domain, and the tester equivalence gives the conjecture over
  `k`.
- Conversely, the conjecture over `k` makes `k[G_U]` a domain.

**(E2).**  Every hyperbolic generalized Rips--Segev group in the setting is torsion-free hyperbolic.  Conversely,
let `alpha beta = 0` in `k[G]` with `G` torsion-free hyperbolic.
- `G` is finitely generated, so take `H = G` in Step 2.  (Subgroups of `G` need not be hyperbolic, which is why the
  whole of `G` is used.)
- `G(Gamma) = G *_{<a>} K_Gamma` is hyperbolic by Step 2 and contains `G`.

## Step 4.  (E3): the support reduction is equivalent to the conjecture

**`SR(k)` implies the conjecture.**
- The hypotheses of `rips-segev-witness-supports-carry-no-zero-divisors` are:
  - `Gr'_*(1/8)` over `F` for arbitrary finitely generated torsion-free factors;
  - at most one pair of distinguished positions at distance one.
- Both hold for Steenbock's table over every `H * Z`.  The first holds by Step 0.  The second holds because the table
  has no distance equal to one.
- So no generalized group in the setting has a zero-divisor pair with `supp alpha` in `A` and `supp beta` in `B`.
- `SR(k)` then says that no such group has any zero-divisor pair.  By (E1), the conjecture holds over `k`.

**The conjecture implies `SR(k)`.**  If the conjecture holds, the hypothesis of `SR(k)` is never met, so `SR(k)`
holds vacuously.

**The failing shape.**  Let `supp alpha` lie in `gH` and `supp beta` in `Hh`, with `H <= G(Gamma)` the factor
subgroup.
- Write `alpha = g alpha_0` and `beta = beta_0 h` with `alpha_0, beta_0 in k[H]`.  Then `alpha beta = g (alpha_0
  beta_0) h`, so `alpha beta = 0` if and only if `alpha_0 beta_0 = 0` in `k[H]`.
- A coincidence `(g x)(y h) = (g x')(y' h)` means `x y = x' y'` in `G(Gamma)`.  By the embedding, this is `x y = x'
  y'` in `H`.
- The element `x y y'^{-1} x'^{-1}` is then a single letter of `G_1 = H` that is trivial in `F`.  Its minimal van
  Kampen diagram over `R` has no faces, and no relator of `Gamma` is involved.
- A support-reduction lemma is a statement about product coincidences and the van Kampen diagrams over `R` that
  witness them.  On these supports every such diagram is empty.
- So a reduction valid for every factor `H` must decide whether `k[H]` is a domain by an argument blind to
  relators.  By (E1) with `H` arbitrary, that is the conjecture itself.
- This is the exact step where a diagram-driven reduction stops: the first coincidence between two
  elements of one `H`-coset.

**What survives.**  For the core groups `K_Gamma`, the factors are `Z` and the factor cosets carry no zero divisors.
So the brief's reduction is not killed there.

## Step 5.  (E4)

The Promislow group `P = <x, y | x^{-1} y^2 x = y^{-2}, y^{-1} x^2 y = x^{-2}>` is finitely generated and
torsion-free.  `F_2[P]` has a unit that is not of the form `lambda g` (Gardam, Ann. of Math. 2021).  Its image under
`F_2[P] -> F_2[P *_{<a>} K_Gamma]`, for any `1 != a in P`, is still a unit with support of size greater than one.

## Step 6.  What the theorem leaves

- **Domain factors.**  Take `G(Gamma) = G_1 *_{<a>} K_Gamma *_{<b>} G_2` with `k[G_1]` and `k[G_2]` domains.
  - This group ring is a domain if (R1) `k[K_Gamma]` is a domain, and (R2) amalgamated products over infinite
    cyclic subgroups of groups with domain group rings have domain group rings.
  - The domain-factor statement implies (R1), because `Z * Z` qualifies.
- **Core groups.**  (R1) for the original presentations is Steenbock's question.  These groups are two-generated,
  hyperbolic, and not uniformly covered by (E1).
- **Not proved here.**  Whether (R1) implies the conjecture, and whether (R2) holds.
