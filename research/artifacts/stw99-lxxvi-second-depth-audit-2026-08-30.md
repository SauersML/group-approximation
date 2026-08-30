# STW LXXVI second-depth audit: positive class and compact obstruction

## New positive boundary

Antoine, Perera, Thiel, and Vilalta,
[Pure C*-algebras](https://arxiv.org/abs/2406.11052), Theorem 6.6, proves a
non-simple case of the desired implication.  If `A` is separable, locally
subhomogeneous, has stable rank one and topological dimension zero, then
pureness and Z-stability are equivalent.  Such a pure `A` is therefore
Cu-regular.  This class is not a restatement of the simple result in STW
Proposition 23 and does not require `A` to be unital.

## Strengthened compact obstruction

For projections `p,q` over `A`, ambient equality in `K_0(A)` is too weak to
support a finite-projection collapse after tensoring with Z.  Put
`J=Ideal(p,q)` and assume `J tensor Z` is stably finite.  Equality of the
Z-stabilized Cu classes is then stable Murray--von Neumann equivalence; its
implementing partial isometry lies in `J tensor Z`.  Since
`J -> J tensor Z` is a KK-equivalence, this forces `[p]=[q]` already in
`K_0(J)`.

Thus a compact counterexample in this stably finite corridor requires all
three conditions:

```text
[p] != [q] in Cu(A),
[p]  = [q] in K_0(Ideal(p,q)),
[p tensor 1_Z] = [q tensor 1_Z] in Cu(A tensor Z).
```

The middle condition excludes the most natural extension construction, where
two ideal projections become equal in ambient K-theory because their
difference is in the image of an index map from the quotient.

## Coherent pure noncancellation that does not collapse

`A=T tensor Z`, with `T` the Toeplitz algebra, is an explicit stress test.
It is non-simple and Z-stable, hence pure and Cu-regular.  The Toeplitz boundary
map kills the inclusion `K_0(K tensor Z)->K_0(A)`.  Rank-two and rank-one
projections in the compact ideal therefore have equal ambient K0 class but
distinct compact Cu classes.  Their difference is nonzero in the ideal's K0,
so the local protection theorem shows it survives every additional Z factor.

This proves that purity does not imply ambient projection cancellation and
that index-boundary noncancellation in a stably finite tensor ideal is the
wrong counterexample mechanism.  The remaining finite compact frontier is
genuinely subtler: stable noncancellation at equal K0 inside one generated
ideal, followed by collapse under Z.

The finiteness qualifier is essential.  In a non-stably-finite algebra,
Cuntz-equivalent projections need not be Murray--von Neumann equivalent; the
Cuntz semigroup can identify infinite projection classes with different K0
classes.  Accordingly the local-K0 theorem does not exclude a second route in
which tensoring with Z makes the images infinite and Cuntz equivalent.  No
such example is claimed.

## Product/reduced-product lane

The product `prod_n Z` is not a counterexample currently justified by the
graph.  First, Problem LXXVI uses the separable convention from STW Definition
24, while this product is nonseparable.  Second, neither

```text
Cu(prod_n Z) = prod_n Cu(Z)
```

nor preservation of almost divisibility follows coordinatewise: stabilization
and uniform compact containment impose uniformity on Cuntz witnesses.  Minimal
tensor product also need not commute with infinite products, so failure of
surjectivity at the C*-level does not by itself imply failure on Cu.

There is evidence against the naive product attack.  Given a finite subset of
`prod_n Z` and `epsilon>0`, one may choose in each coordinate a unital copy of
Z that is `epsilon`-central for that coordinate's finite set; the coordinatewise
copies define a uniformly approximately central embedding into the product.
The standard absorption criterion is normally stated for separable algebras,
so this observation is not promoted here to Z-stability of the product.  It
does show that a claimed product counterexample needs a nonseparable absorption
theorem or an explicit uniform Cu witness, neither of which is presently in
hand.

## Open frontier

No compact counterexample was produced.  A stably finite one must evade both
the zero-dimensional locally subhomogeneous positive theorem and ideal-local
K0 protection.  In particular, an extension boundary class in a stably finite
generated tensor ideal cannot be the element that disappears after
Z-stabilization.  The alternative infinite-projection corridor remains open.
