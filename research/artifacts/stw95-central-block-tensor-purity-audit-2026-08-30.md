# STW Problem XCV: central block tensor-purity audit (2026-08-30)

## Result

A single pure algebra `P` with pure tensor square generates a larger tensor
permanence class after adjoining arbitrary Z-stable central blocks and taking
finite or countable `c_0`-sums.  Two algebras assembled from those blocks are
pure, and their minimal tensor product is the `c_0`-sum of the pairwise block
products, all of which are pure.

The free-group seed `P=C*_r(F_2)` gives a strict instance.  Adding a block
`N tensor Z` for a separable nonexact `N` produces pure factors which are
nonsimple, nonexact, and non-Z-stable, while their tensor product remains
pure.

## Direct-sum audit

For a finite direct sum, `Cu` is the direct sum of the component semigroups.
Almost unperforation is coordinatewise.  For almost divisibility, divide
each coordinate of a way-below pair and take the finite tuple of divisors.

A countable `c_0`-sum is the sequential inductive limit of its finite partial
sums.  The already established sequential permanence theorem therefore
supplies purity; no unsupported formula for `Cu` of an infinite product is
used.  The minimal tensor identity

```text
(direct_sum_i A_i) tensor_min (direct_sum_j B_j)
  ~= direct_sum_(i,j) (A_i tensor_min B_j)
```

is spatial and needs no exactness.  It can be checked on finite central
rectangles, where the norm is the maximum of the block norms, and then
completed.

## Local-product audit

There are only two local cases.  The seed-seed product is pure by hypothesis.
Every other pair has a Z-stable coordinate, so associativity moves an
absorbed copy of `Z` into the product and makes that block product Z-stable.
Thus the proof never infers concrete tensor purity from purity of the
abstract Cu tensor product.

For `P=C*_r(F_2)`, the repository's established first-half counterexample
proves `Cu(P)=Cu(Z)`.  Purity of `P tensor P` follows separately: exact
selflessness tensors to selflessness; Robert then supplies stable rank one,
strict comparison, and a unique quasitrace; Thiel's stable-rank-one rank
theorem supplies all ranks, hence almost divisibility.  Strict comparison
and almost divisibility are purity.  The extra compact K-theory classes in
the tensor square are harmless here: the result uses only purity of the local
block, not a claim that its Cuntz semigroup is `Cu(Z)`.

## Strictness audit

Let `N` be a unital separable nonexact C-star algebra and set
`R=N tensor Z`.  Then `R` is Z-stable but nonexact, since `N` embeds in it
and exactness is hereditary to subalgebras.  For

```text
A=C*_r(F_2) direct_sum R,
```

the two summands are pure, so `A` is pure.  The algebra is nonexact and
nonsimple.  It is not Z-stable because Z-stability passes to quotients while
`C*_r(F_2)` is not Z-stable; the latter follows from the full non-McDuff
factor `L(F_2)` in its unique-trace GNS representation.

Thus neither factor in `A tensor A` is Z-stable or exact.  The factors are
not selfless because selfless algebras are simple, and they are not ASH
because ASH algebras are nuclear.  This places the example outside the
one-Z-stable-factor, exact/selfless, exact-filtration, ASH-layered, and
nuclear-simple-layer results.  It is nevertheless centrally decomposable;
no claim is made for indecomposable nonexact factors.

## Literature and limitation

The current Cairn graph and a primary-title/abstract search found no node
recording this block-closure theorem.  Its ingredients are standard or
already established, so no literature-priority claim is made.

The conclusion depends completely on the central `c_0` decomposition and on
purity of the single seed square.  It gives no information about an
indecomposable pair, about arbitrary extensions coupling the blocks, or
about the unresolved entangled classes in `Cu(A tensor_min B)`.
