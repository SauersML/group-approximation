---
rg: 2
id: tail-uniform-germ-extensions-of-v-are-not-fp
kind: claim
title: Extending V by homeomorphisms whose singular germs are read off one non-eventually-periodic tail never gives a finitely presented group unless every added germ is already a V-germ
distinct_from:
  orbit-preserving-germ-corollary-extensions-of-v-are-rational: that derives rationality from the Belk--Hyde--Matucci germ hypotheses, which already force eventually periodic singular points; this assumes no germ hypothesis and derives the same conclusion, for tail-uniform generators, from finite presentation alone.
  bhm-singfix-condition-forces-fp-germ-groups: that says a BHM hypothesis forces finitely presented germ groups; here the germ group of the main example is Z, finitely presented, and the whole group is still not finitely presented.
  fp-bounded-displacement-e2-envelopes-are-eventually-periodic: that is the analogous conclusion for E_2 shift envelopes on N, proved by pumping unique solutions of relators; this is for extensions of Thompson's group V on Cantor space, proved by locality of marked relations in the tail parameter, and no uniqueness or pumping enters.
  rational-homeomorphism-subgroups-have-exponential-wp: that bounds the word problem of rational groups; this shows that inside the tail-uniform class finite presentation forces rationality, so that bound applies to every finitely presented member.
---

**ESTABLISHED** by `tail-uniform-germ-extensions-of-v-are-not-fp-proof`.

## Setting

`C = {0,1}^N`. For a finite word `w`, `C(w)` is its cylinder. For a point `y`,
`y|n` is its prefix of length `n`, `y_i` its `i`-th bit, `σ` the shift, and `¬`
bit complement. Products are compositions.

A **tail template** `τ` is a finite list of data of two kinds.
- *Prefix pairs* `u_i -> u'_i`, for `i = 1..s`.
- *Singular data* `(a_k, j_k, n_k ; a'_k, j'_k, δ_k)`, for `k = 1..r`. Here
  `a_k, a'_k` are words, `j_k, j'_k >= 0`, `n_k >= 1` and `n_k + δ_k >= 1`.

For `y ∈ C` put:
- `z_k(y) = a_k σ^(j_k) y` and `z'_k(y) = a'_k σ^(j'_k) y`;
- `W_k(y) = C(a_k (σ^(j_k)y)|n_k)` and `W'_k(y) = C(a'_k (σ^(j'_k)y)|(n_k+δ_k))`.

`τ` is **admissible at `y`** when two conditions hold:
- the sets `C(u_i)` and `W_k(y)` partition `C`;
- the sets `C(u'_i)` and `W'_k(y)` partition `C`.

Then the **template map** `g_(τ,y)` is defined piece by piece.
- On `C(u_i)` it is the prefix replacement `u_i q -> u'_i q`.
- On `W_k(y)` it sends `z_k(y) -> z'_k(y)`. For every `n >= n_k` it also sends

      a_k (σ^(j_k)y)|n  ¬(σ^(j_k)y)_(n+1)  q   ->   a'_k (σ^(j'_k)y)|(n+δ_k)  ¬(σ^(j'_k)y)_(n+δ_k+1)  q.

  This is a *relative shift*. The point at deviation depth `n` from `z_k(y)`
  goes to deviation depth `n + δ_k` from `z'_k(y)`, and the tail `q` is kept.

The **tail offset** of datum `k` is `o_k = j'_k + δ_k - j_k`.

Elements of `V` are template maps with no singular data. For a
non-eventually-periodic `x`, a singular germ of `g_(τ,x)` is the germ of an
element of `V` exactly when its offset is `0` (Lemma D of the proof).

## Statement

Let `x ∈ C` be not eventually periodic. Let `τ_1, ..., τ_m` be tail templates
admissible at `x`, and put `G = < V, g_(τ_1,x), ..., g_(τ_m,x) >`. If some `τ_i`
has a singular datum with nonzero tail offset, equivalently some `g_(τ_i,x)` has
a singular germ that is not a germ of `V`, then **`G` is not finitely presented**.

**Corollary (every finitely presented member is rational).** Let
`G = < V, g_(τ_1,x), ..., g_(τ_m,x) >` for any `x ∈ C` and any templates
admissible at `x`. If `G` is finitely presented, then `G` consists of rational
homeomorphisms, and by `rational-homeomorphism-subgroups-have-exponential-wp`
its word problem is in time `2^O(n)`.
- If `x` is eventually periodic, every template map is rational.
- Otherwise every offset is `0`, so every generator is locally a prefix
  replacement everywhere, hence lies in `V`, and `G = V`.

## Main example

For `x ∈ C` let `A_n = C(x|n ¬x_(n+1))`. Define `h_x` as follows:
- it fixes `x`;
- for `n >= 2` it maps `A_n` onto `A_(n-1)` by the prefix replacement
  `x|n ¬x_(n+1) -> x|(n-1) ¬x_n`;
- it maps `A_0` and `A_1` onto the two halves of `A_0` by
  `¬x_1 -> ¬x_1 0` and `x_1 ¬x_2 -> ¬x_1 1`.

This is the template map of
`τ = { ¬x_1 -> ¬x_1 0 ,  x_1¬x_2 -> ¬x_1 1 ;  (ε, 0, 2 ; ε, 0, -1) }`, with
offset `-1`. So **`< V, h_x >` is not finitely presented for any
non-eventually-periodic `x`**, computable or not.

Its word problem still carries all of `x`. Suppose `x|M` is known, with
`M >= 2`. Put `P = x|M 0` and `P' = x|(M-1) ¬x_M`. Let `f` swap `C(P0)` with
`C(P1)`, and let `f'` swap `C(P'0)` with `C(P'1)`. Then
`h_x f h_x^-1 = f'` if and only if `x_(M+1) = 1`.
- If `x_(M+1) = 1`, then `C(P) = A_M` is mapped by `P -> P'`.
- If `x_(M+1) = 0`, then `h_x(C(P)) = C(x|M)`, which is disjoint from `C(P')`.

The query words are computable from `x|M`, and their length is bounded by a
recursive function of `M` that does not depend on `x`. So for every recursive
bound some computable `x` gives `< V, h_x >` a word problem beyond it. This is
the "hardness in one free tail parameter" source of hard germ extensions, and
the theorem shows that no such group is finitely presented.

## What it kills

The class is every finitely generated extension of `V` whose extra generators
are tail-uniform, meaning their singular germs are relative shifts along
shifted copies of a single parameter point `x`.
- *Invariant.* Whether each relation holds is decided by a finite prefix of the
  parameter (Lemma C, locality). A nonzero tail offset makes one
  conjugation relation read a bit of `x` at arbitrary depth.
- *Where every member dies.* At finite presentation. A finite relator set is
  certified on a cylinder around `x`, and flipping one deep bit of `x` inside
  that cylinder gives a marked group in which every relator holds but the
  conjugation relation fails.

So the class supplies no witness to the following:
- `fp-simple-groups-with-arbitrarily-complex-word-problem`;
- `type-a-actors-with-arbitrarily-hard-word-problem`, through
  `fp-full-binary-cantor-groups-have-type-a-actions`.

Every finitely presented member is rational, and
`complexity-bounded-host-classes-are-not-universal` applies to the class.

The mechanism is the classical one for Grigorchuk's groups `G_ω`. The marked
group depends continuously on the parameter, and a finitely presented marked
group has a neighbourhood made of its own marked quotients. Here the parameter
is the tail `x`, and the nonzero offset supplies nearby parameters that are not
quotients.

## Not covered

The proof uses that each generator is read off the *same* point `x` by a
*finite* template. Two routes stay open:
- generators whose germs at a singular point apply unboundedly many different
  rules, so they are not a single relative shift;
- germ groups given by other finitely presented groups acting on the tail, as
  for shell envelopes.
