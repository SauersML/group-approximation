# The ambient Bernoulli group does not Haar-groupify Manzoor's IRS

Date: 2026-08-14

## 1. Outcome

The subgroup space of a free group sits naturally inside a compact binary
group:

```text
Sub(F) subset {0,1}^F.
```

Conjugation by `F` permutes the coordinates of `{0,1}^F`, so it acts by
continuous group automorphisms and preserves product Haar measure. This does
not turn Manzoor's non-co-hyperlinear IRS into the algebraic Haar action from
`ALGEBRAIC_HAAR_NONCE_TO_NONHYPERLINEAR.md`.

There are two exact obstructions.

1. `Sub(F)` has product-Haar measure zero in `{0,1}^F`.
2. The canonical Haar measure which really is supported on subgroups—take
   kernels of random binary characters—has an amenable, hence
   Connes-embeddable, GNS algebra.

Thus the fact that the IRS construction uses probability measures on a
binary shift is not a hidden semidirect-product groupification.

## 2. The subgroup locus has Haar measure zero

Let `Gamma` be any countably infinite group and give

```text
B={0,1}^Gamma
```

coordinatewise addition and product Haar probability `nu`. Regard a subset
of `Gamma` as its indicator in `B`.

**Proposition 1.** `nu(Sub(Gamma))=0`.

**Proof.** Choose pairs `(a_n,b_n)` inductively so that the coordinate triples

```text
{a_n,b_n,a_n b_n}
```

are pairwise disjoint. At each stage only finitely many choices are
forbidden, so infinitude of `Gamma` permits the next pair.

For each `n`, the event

```text
xi(a_n)=xi(b_n)=1,       xi(a_n b_n)=0               (MHA1)
```

has probability `1/8`. The events are independent because their coordinate
triples are disjoint. An indicator satisfying `(MHA1)` is not closed under
multiplication and hence is not a subgroup. Therefore

```text
nu(Sub(Gamma)) <= (7/8)^N
```

for every `N`, proving the claim. End proof.

Conditioning the identity coordinate to equal `1` does not help: the triples
can be chosen away from the identity and the same proof applies.

Consequently one cannot restrict ambient Bernoulli Haar measure to
`Sub(F)`. The subgroup locus is a null, nonlinear constraint set. Manzoor's
separating IRS is instead obtained as a weak-star cluster point of arbitrary
pseudo-subgroup probability measures in the NPA compactness argument. The
construction supplies no translation-invariant group law for that measure.

## 3. The natural Haar-supported repair is CE

There is a genuine compact group whose Haar points parameterize subgroups.
Let

```text
X=Hom(Gamma,C2)
```

with pointwise addition and Haar probability, and send

```text
chi |-> ker(chi).
```

Every kernel is normal, so the pushforward is an IRS. Put

```text
N=intersection_(chi in X) ker(chi)
  =[Gamma,Gamma] Gamma^2.                             (MHA2)
```

For fixed `g`, evaluation `chi |-> chi(g)` is either the zero map or a
surjective continuous homomorphism to `C2`. Haar invariance therefore gives

```text
P(g in ker(chi)) = 1       if g in N,
                     1/2   if g notin N.             (MHA3)
```

The IRS character is consequently

```text
tau=(1/2) 1_Gamma + (1/2) 1_N.                       (MHA4)
```

Here `1_Gamma` is the trivial character and `1_N` is the pullback of the
regular character of `Gamma/N`. Its GNS representation is the direct sum of
the trivial and regular representations of `Gamma/N`, so its von Neumann
algebra is an image of

```text
C direct-sum L(Gamma/N).                              (MHA5)
```

If `Gamma/N` is infinite, the two traces are mutually singular and this is
the displayed direct sum; in the finite case the image may identify the
redundant trivial summand. Either way `Gamma/N` is elementary abelian of
exponent two, so the GNS algebra is amenable and Connes embeddable.

Thus the most natural way to replace the null subgroup locus by a compact
Haar family produces exactly the wrong sector: an amenable quotient rather
than Manzoor's non-CE IRS algebra.

## 4. Exact Fourier-basis criterion

The obstruction can be stated without mentioning a preferred model of the
probability space. A p.m.p. action `G` on `(X,mu)` is measurably conjugate to
the dual action on a compact metrizable abelian group with Haar measure if
and only if `L^2(X,mu)` has a countable orthonormal basis `A` of
circle-valued functions such that

```text
1 in A,
A is closed under multiplication and complex conjugation,
G permutes A by group automorphisms.                  (MHA6)
```

Indeed such an `A` is a countable discrete abelian group, its characters
identify `(X,mu)` with `dual(A)` and Haar measure, and the last condition
identifies the action. Conversely the ordinary characters of a compact
abelian group give `(MHA6)`.

Under `(MHA6)`, Fourier transform gives

```text
L_infinity(X,mu) crossed G ~= L(A semidirect G).      (MHA7)
```

If `G` is sofic, then `A semidirect G` is amenable-by-sofic and hence sofic;
the algebra in `(MHA7)` is Connes embeddable. Therefore the non-CE free-group
action obtained from Manzoor's IRS cannot admit a basis `(MHA6)`.

This is the precise missing structure in the algebraic-Haar route. A mere
compact binary realization, a coordinate-permutation action, or a nonatomic
measure-space identification does not supply a multiplicative Fourier basis.

## 5. Consequence for the nonhyperlinear program

The algebraic-Haar bridge remains valid and decisive, but Manzoor's source
cannot instantiate it by ambient Bernoulli completion. A successful use of
that bridge must construct a different non-CE action whose probability
algebra already has `(MHA6)`, and its acting group cannot lie in the sofic
case covered by amenable-extension permanence.

Equivalently, one must build the multiplication law on the Fourier labels at
the same time as the non-CE trace. Adding that law after the IRS compactness
argument replaces the separating measure by Haar and erases the obstruction.

## Primary source

Manzoor's revised proof constructs the IRS as a weak-star cluster point in
the pseudo-subgroup NPA hierarchy and then uses an abstract p.m.p. realization;
it does not select Haar measure on a compact group:

- A. Manzoor, *There is an equivalence relation whose von Neumann algebra is
  not Connes embeddable*, arXiv:2502.06697v2, Theorem 2.4, Theorem 3.6, the
  proof of Theorem 3.13, and the proof of Theorems 1.1--1.2.
