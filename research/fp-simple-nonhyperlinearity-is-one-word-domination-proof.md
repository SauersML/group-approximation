---
rg: 2
id: fp-simple-nonhyperlinearity-is-one-word-domination-proof
kind: route
title: Identify one word with the hyperlinear radical and remove character phases by conjugate doubling
target: fp-simple-nonhyperlinearity-is-one-word-domination
requires:
  - hyperlinear-radical-presentation-compactness
  - character-domination-collapse-equivalences
---

Write `F=F(S)`, let `p:F ->> G` be the presentation map, and put
`wbar=p(w)!=1`.

## Simplicity turns one radical word into nonhyperlinearity

Use the tracial-matrix-ultraproduct definition of the hyperlinear radical.
We first prove

```text
wbar in Rad_hyp(G)  iff  G is nonhyperlinear.           (FS2)
```

If `G` is hyperlinear, a hyperlinear embedding of `G` into a tracial matrix
ultraproduct is injective and therefore does not kill `wbar`.  Thus `wbar`
is not in the radical.

Conversely, suppose `wbar` is not in the radical.  There is a homomorphism

```text
rho:G -> U(prod_omega M_(d_n)(C))
```

with `rho(wbar)!=1`.  In particular `rho` is nontrivial.  Its kernel is a
proper normal subgroup of the simple group `G`, hence is trivial.  Thus
`rho` is a hyperlinear embedding and `G` is hyperlinear.  This proves
`(FS2)`.  Notice that simplicity is used on the kernel of an arbitrary
nontrivial ultraproduct homomorphism, not on any individual coordinate map.

## The normalized-HS formulation

Apply `hyperlinear-radical-presentation-compactness` to `G`, `wbar`, and the
finite presentation above.  Since the relator list is finite, its finite
window may be taken to be all of `R`.  It gives exactly

```text
wbar in Rad_hyp(G)  iff  condition 2.                   (FS3)
```

Together with `(FS2)`, this proves the equivalence of conditions 1 and 2.

## The phase-insensitive character formulation

Regard every tuple `U in U(d)^S` as an exact finite-dimensional unitary
representation `pi_U` of the free group `F`.  If `chi_U` is its normalized
character, set

```text
q_U(g)=1-|chi_U(g)|^2,
Q_R(U)=sum_(r in R) q_U(r).
```

Let `FD-collapse` denote the qualitative assertion

```text
Q_R(U_n) -> 0  implies  q_(U_n)(w) -> 0                (FS4)
```

for every sequence of finite-dimensional tuples, with dimensions allowed to
vary.  The unitary half of
`character-domination-collapse-equivalences`, applied to the group `F`, the
finite subset `R` and the element `w`, says precisely that `(FS4)` is
equivalent to the existence of the dimension-independent constant in
`(FS1)`.

It remains to identify `(FS4)` with hyperlinear-radical membership.  This is
where scalar phases are removed.

Suppose `(FS4)` fails.  After passing to a subsequence there are an
`eta>0` and tuples `U_n` such that

```text
Q_R(U_n) -> 0,            q_(U_n)(w) >= eta.            (FS5)
```

Replace `pi_(U_n)` by its conjugate double
`pi_(U_n) tensor conjugate(pi_(U_n))`.  Its normalized character at `g` is
`|chi_(U_n)(g)|^2`, and therefore

```text
||(pi_(U_n) tensor conjugate(pi_(U_n)))(g)-I||_2^2
  = 2(1-|chi_(U_n)(g)|^2)
  = 2q_(U_n)(g).                                           (FS6)
```

The relators consequently converge to the identity in normalized HS norm,
whereas `w` stays at distance at least `sqrt(2 eta)`.  The metric
ultraproduct homomorphism factors through `G` and retains `wbar`.  Hence
`wbar` is not in `Rad_hyp(G)`.

For the converse, suppose `wbar` is not in `Rad_hyp(G)`.  Choose a
homomorphism from `G` to a hyperlinear group which retains `wbar` (for
example, take the image of a detecting homomorphism into a tracial matrix
ultraproduct).  Its image is countable.  Use the regular-character
formulation of hyperlinearity for that image and lift the matrices assigned
to the images of `S` to tuples `U_n`.  After a diagonal choice over the
finite relator set,

```text
q_(U_n)(r) -> 0  for every r in R,
q_(U_n)(w) -> 1,
```

because every relator is the identity in the image while `wbar` is not.
Thus `(FS4)` fails.  We have proved

```text
FD-collapse  iff  wbar in Rad_hyp(G).                  (FS7)
```

Combining `(FS7)` with `character-domination-collapse-equivalences` and
then with `(FS2)` proves the equivalence of conditions 1 and 3.

Equation `(FS6)` is also the reason no direct comparison between conditions
2 and 3 is being asserted.  The defect `q_U` ignores a scalar relator phase;
the ordinary normalized-HS defect does not.  Both conditions characterize
the same radical membership, but the character route first passes to the
conjugate double, where every scalar phase cancels.
