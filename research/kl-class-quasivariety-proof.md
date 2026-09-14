---
rg: 2
id: kl-class-quasivariety-proof
kind: route
title: Finite collapse certificates turn Kervaire--Laudenbach into quasi-identities
target: kl-class-is-a-quasivariety
requires: []
---

Fix `D`.  Throughout, a word over a group `G` in the free product `G * <t>`
is a finite alternating product of *syllables* from `G` and from `<t>`.

## Step 0. Certificates are finite

Let `1 != a in G` die in `G_w`.  Then in `G * <t>`

    a  =  prod_(j=1..n) u_j w^(e_j) u_j^(-1)                                   (*)

for some `u_j in G * <t>` and `e_j = ±1`.  Write the right side as a formal
syllable word, writing each inverted factor (`u_j^(-1)`, and `w^(-1)` when
`e_j = -1`) by inverting its syllables in reverse order.  The free product
normal form reduces it to the one-syllable word `a` by finitely many moves:
- multiply two adjacent `G`-syllables `x, y` into `xy`;
- add adjacent `t`-exponents;
- delete a syllable equal to `1` or `t^0`.

Let `F subset G` be the finite set of all `G`-elements occurring as syllables
at any stage, together with `1`, `a`, and the inverse of every such element.
Take a letter `[x]` for each `x in F`, and let `T` be the finite set of
relators
- `[1]`;
- `[x][x^(-1)]` for `x in F`;
- `[x][y][z]^(-1)` for each move multiplying `x, y` into `z = xy`.

Put

    P_F = < [x], x in F | T > .

Every move is a consequence of `T` inside `P_F * <t>`.  A multiplication move
uses the third kind of relator, a deletion of `1` uses `[1]`, and the syllable
of `x^(-1)` coming from a formal inverse equals `[x]^(-1)` by the second kind.
So (*) holds in `P_F * <t>`, with `w` read over `P_F` through the letters of
its coefficients, and the `t`-exponent sum is unchanged.  The map
`[x] -> x` satisfies `T` in `G`, so it defines `P_F -> G`, and it sends
`alpha := [a]` to `a != 1`.  So `alpha != 1` in `P_F`.

## Item 1. Quasi-identities

*(If `G ∉ KL_D` then some `sigma_c` fails in `G`.)*  Take a failure `(G, w, a)`
and form `P_F` as in Step 0, with `x = F` and `r_i` the relations `T`.  Then
`c = (P_F, w, alpha)` is a template, since (*) holds in `P_F * <t>`.  The
assignment `x -> F subset G` satisfies every `r_i`, and `alpha` evaluates to
`a != 1`, so `G` violates `sigma_c`.

*(If some `sigma_c` fails in `G` then `G ∉ KL_D`.)*  Suppose `g in G^x`
satisfies every `r_i` while `alpha(g) != 1`.  Then `x -> g` defines a
homomorphism `phi : P -> G`.  It extends to `P * <t> -> G * <t>` fixing `t`,
so it preserves `deg_t` and carries the identity expressing `alpha` in
`<<w>>` to an identity in `G * <t>`.  So `alpha(g) != 1` dies in
`G_(phi(w))` with `deg_t(phi(w)) in D`.

*Recursive enumerability.*  Finite presentations and words can be
enumerated.  For each, the identities (*) in `P * <t>` are the consequences of
the finite presentation `<x, t | r_1, ..., r_k, w>`, which can be enumerated.

## Item 2. Closure

Quasi-identities hold in the trivial group, and pass to subgroups (restrict
the witness) and to products (if the premises hold coordinatewise, so does the
conclusion).  They pass to ultraproducts by Łoś's theorem: a quasi-identity is
a first-order sentence.

*Directed unions and finitely generated subgroups.*  A violating assignment
`g` involves finitely many elements, which lie in a finitely generated
subgroup that already violates `sigma_c`.  Subgroup closure gives the
converse.

*Residual.*  Let `G` be residually `KL_D` and suppose `g` violates `sigma_c`.
Choose `phi : G -> Q` with `Q in KL_D` and `phi(alpha(g)) != 1`.  Then
`phi(g)` satisfies the premises, since `phi` is a homomorphism, and not the
conclusion, so `Q` violates `sigma_c`.  That is a contradiction.  Subdirect
products are residually their factors.

*Local embeddings.*  Let `g` violate `sigma_c` in `G`.  Let `E subset G` be the
finite set of all partial products needed to evaluate each `r_i(g)` and
`alpha(g)` letter by letter, together with `1` and the inverses of the entries
of `g`.  Suppose `psi : E -> Q` is injective, multiplicative whenever
`x, y, xy in E`, and `Q in KL_D`.  Evaluating letter by letter, `psi` carries
each evaluation to the corresponding evaluation at `psi(g)`.  So
`r_i(psi(g)) = psi(1) = 1`, where `psi(1) = psi(1 * 1) = psi(1)^2` forces
`psi(1) = 1`.  Also `alpha(psi(g)) = psi(alpha(g)) != psi(1)` by injectivity.
So `Q` violates `sigma_c`, a contradiction.

## Item 3. Radical bound

Let `a in ker(G -> G_w)` and `phi : G -> Q` with `Q in KL_D`.  Extending `phi`
over `<t>` carries (*) into `Q * <t>`, so `phi(a)` dies in `Q_(phi(w))`.  The
map `Q -> Q_(phi(w))` is injective because `deg_t(phi(w)) = deg_t(w) in D`, so
`phi(a) = 1`.

## Item 4. The conjecture

`sigma_c` holds in every group if and only if it holds in `P` at the
generating tuple, since every assignment factors through `P`.  That is exactly
`alpha = 1` in `P`.  So `KL_D` is every group if and only if no template has
`alpha != 1` in `P`.

## Remarks

- The overgroup statement ("every overgroup of a counterexample is a
  counterexample") is the contrapositive of subgroup closure.
- The consequences listed on the claim for hyperlinear and MF groups use only
  item 2 and the two established theorems named there. They are commentary,
  not part of this route's proof commitment.
