# STW Problem LXXIV: zero-dimensional Cartan property-SP audit (2026-08-30)

## Result

Every separable unital C-star algebra with a Cartan subalgebra having
zero-dimensional spectrum has property (SP).  Therefore a simple such
algebra in which every nonzero projection is infinite is purely infinite.

This is a structural positive class for Problem LXXIV.  It does not assume
that the ambient algebra has real rank zero, is nuclear, or has any Cuntz
comparison property.

## Exact cutdown mechanism

For a Cartan pair `D subset A`, Renault reconstruction gives a twisted
topologically principal etale groupoid.  The standard finite-bisection
shrinking argument supplies, for every nonzero `a>=0`, a diagonal
contraction `f` for which

```text
f a f ~= f E(a) f
```

in norm while the right side retains almost all of `||E(a)||`.  The
expectation is faithful, so this norm is positive.

Zero-dimensionality is used at exactly one point: choose a nonempty clopen
set on which `f` is bounded below and `fE(a)f` has a uniform positive lower
bound.  Its characteristic projection `p` then satisfies

```text
(pfp)(pap)(pfp) >= delta p
```

for some `delta>0`.  Both the outer factors and their product with `pap`
are invertible in `pAp`, hence `pap` itself is invertible.  The polar
partial isometry of `a^(1/2)p` moves `p` to a nonzero projection in
`Her(a)`.

The last move is important: the diagonal projection need not itself lie in
the hereditary algebra.  Invertibility of its compression is what produces
the Murray--von Neumann equivalent projection which does.

## Hypothesis audit

* **Separability** is used for Renault's second-countable Weyl groupoid and
  the finite-support approximation.
* **Unitality** makes the Cartan spectrum compact, so a clopen set gives a
  projection in `C(X)` without a separate compact-support choice.
* **Cartan regularity and maximal abelianness** produce the topologically
  principal Weyl groupoid and its finite bisection normalizers.
* **Faithfulness of the Cartan expectation** ensures `E(a)!=0`.
* **Zero-dimensionality** supplies the clopen spectral cut.

No groupoid amenability is used; the statement applies equally to nuclear
and nonnuclear Cartan pairs.  The twist causes no change because diagonal
compression depends only on the source and range of each bisection.

## Relation to the existing frontier

The theorem reaches the LXXIV hinge directly by proving property (SP).  It
does not descend a projection already found at a matrix level, invoke a
homogeneous coefficient island, or collapse a finite Cuntz root through
comparison.  In the groupoid picture, the distinguished clopen diagonal
projections supply the missing level-one projective root locally inside
every positive element.

The relevant primary sources are:

* Jean Renault, *Cartan subalgebras in C-star-algebras*, Irish Math. Soc.
  Bulletin 61 (2008), 29--63, for twisted Weyl-groupoid reconstruction;
* Jonathan Brown, Lisa Orloff Clark, and Adam Sierakowski, *Purely infinite
  C-star-algebras associated to etale groupoids*, Ergodic Theory and
  Dynamical Systems 35 (2015), 2397--2411,
  DOI `10.1017/etds.2014.47`, Lemma 3.1, for the exact
  topologically-principal diagonal cutdown in the untwisted notation.

The route writes the finite-bisection argument and the clopen-gap upgrade
explicitly, including the twisted case.
