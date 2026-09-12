# An algebraic Haar non-CE action would give a nonhyperlinear group

Date: 2026-08-13

## 1. Exact transfer theorem

Let `A` be a countable discrete abelian group and let a countable group `G`
act on `A` by automorphisms. Put

```text
K=dual(A),                    H=A semidirect G.          (AHN1)
```

The compact metrizable abelian group `K` carries Haar probability measure,
and the dual action of `G` preserves it.

**Theorem 1.** There is a canonical trace-preserving isomorphism

```text
L(H) ~= L_infinity(K,Haar) crossed G.                  (AHN2)
```

Consequently, if the crossed product on the right of `(AHN2)` is not
Connes embeddable, then the explicit discrete semidirect product `H` is not
hyperlinear.

**Proof.** Fourier transform gives a trace-preserving isomorphism

```text
L(A) ~= L_infinity(dual(A),Haar).                      (AHN3)
```

It intertwines the action of `G` on the group unitaries of `A` with the
dual action on `K`. Taking crossed products gives

```text
L(A semidirect G)=L(A) crossed G
                 ~=L_infinity(K,Haar) crossed G.       (AHN4)
```

The canonical coefficient-of-the-identity trace becomes Haar integration
followed by the crossed-product expectation, so `(AHN4)` preserves traces.
Hyperlinearity of `H` is equivalent to Connes embeddability of `L(H)`.
End proof.

This criterion is stronger than merely finding a non-CE p.m.p. action. It
requires the probability algebra to be the Haar algebra of a compact
abelian group and the action to consist of continuous group automorphisms.

## 2. Why Manzoor's IRS does not presently satisfy the criterion

Manzoor constructs a non-co-hyperlinear IRS `mu` of a free group `F`. Its
trace is

```text
tau_mu(g)=mu({H subgroup F : g in H}),                 (AHN5)
```

and the non-CE algebra is the GNS algebra

```text
L(F/mu)=pi_(tau_mu)(F)''.                              (AHN6)
```

Equivalently, choose a p.m.p. action realizing `mu` as its stabilizer
distribution. The algebra `(AHN6)` embeds in the von Neumann algebra of the
orbit equivalence relation. The isotropy is essential: `(AHN5)` records the
positive-measure fixed-point sets.

The general realization theorem used there produces an action on a compact
space with an invariant Borel probability measure. It does **not** make the
space a compact abelian group, the measure Haar, or the action algebraic.
Thus it does not identify `(AHN6)` or the relation algebra with a group
factor by `(AHN2)`.

In fact, for Manzoor's free acting group there is an absolute obstruction.
The group `A` in `(AHN1)` is amenable and `F` is sofic. Soficity is closed
under extensions with amenable kernel, so

```text
A semidirect F is sofic.                                (AHN7)
```

Its group factor, and hence the Haar algebraic crossed product in `(AHN2)`,
is Connes embeddable. Therefore Manzoor's non-CE IRS algebra cannot embed
trace-preservingly into a Haar algebraic crossed product of a countable
abelian group by the same free group. The proposed transfer is a useful
criterion for other acting groups, but it is a proved no-go for this source.

There are two tempting but invalid shortcuts.

1. Taking the diagonal product with a free Bernoulli action makes the group
   action free, but changes every stabilizer to the identity. It destroys
   `(AHN5)` rather than embedding the IRS algebra as the corresponding
   relation algebra.
2. Identifying the underlying nonatomic probability space with a compact
   abelian Haar space is only a measure-space isomorphism. It does not
   conjugate the acting transformations to group automorphisms.

## 3. Sharp remaining target

Either of the following would solve universal hyperlinearity negatively:

1. construct a countable abelian `A` and an algebraic action
   `G -> Aut(A)` whose Haar crossed product in `(AHN2)` is non-CE; or
2. starting from a group outside the amenable-by-sofic closure argument,
   embed a non-CE action algebra trace-preservingly into a Haar algebraic
   crossed product.

The second statement must retain isotropy. A construction which merely
realizes the same p.m.p. orbit relation after adding a free coordinate is
insufficient.

There is also no shortcut through the ambient binary shift containing the
subgroup space. Product Haar measure on `{0,1}^F` gives measure zero to
`Sub(F)`: infinitely many independent multiplication-closure tests each
fail with probability `1/8`. The canonical Haar-supported alternative,
obtained from kernels of random maps `F->C2`, has character
`(1/2)1+(1/2)1_N` for `N=[F,F]F^2`, so its GNS representation is built from
the trivial and regular representations of the amenable quotient `F/N`.
See
`FALSE_MANZOOR_IRS_AMBIENT_HAAR_GROUPIFICATION.md`.

## References

- A. Manzoor, *There is an equivalence relation whose von Neumann algebra
  is not Connes embeddable*, arXiv:2502.06697v2, especially Theorem 1.2 and
  Definitions 2.8--2.12.
