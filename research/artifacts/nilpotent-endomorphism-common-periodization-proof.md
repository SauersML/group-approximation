# Common marked periodizations for torsion-free nilpotent endomorphisms

## Hirsch length forces finite-index image

Let `Gamma` be finitely generated nilpotent and let
`phi:Gamma->Gamma` be injective.  Finitely generated nilpotent groups are
polycyclic, so Hirsch length is defined and invariant under isomorphism.
Thus

```text
h(phi(Gamma))=h(Gamma).
```

For subgroups of a finitely generated nilpotent group, equality of Hirsch
length is equivalent to finite index.  One proof inducts along the lower
central series: the Hirsch length is the sum of the ranks of the successive
abelian factors; equality forces full rank in each factor, hence finite index
one factor at a time.  Therefore `phi(Gamma)` has finite index in `Gamma`.

Let `A=Gamma_ab` and let `T` be its finite torsion subgroup.  The image of
`phi(Gamma)` in `A` has finite index, because

```text
A / image(phi(Gamma))
 = Gamma / (phi(Gamma)[Gamma,Gamma])
```

is a quotient of the finite coset set of `phi(Gamma)`.  Hence the induced
endomorphism of the free abelian group `A/T` has full rank and nonzero
determinant.

## The prime and the pro-p automorphisms

For finitely many injective endomorphisms, choose a prime `p` which divides
neither `|T|` nor any of the nonzero determinants just obtained.  Then

```text
H_1(Gamma;F_p) = A tensor F_p = (A/T) tensor F_p,
```

and every endomorphism acts invertibly on this vector space.

Gruenberg's theorem says that every finitely generated torsion-free nilpotent
group is residually a finite `p`-group for every prime `p`.  Thus `Gamma`
embeds in its pro-`p` completion `P`, and the marked `1!=y` remains
nonidentity.  Each endomorphism extends continuously to `P`.  The canonical
identification

```text
P/Phi(P) = H_1(Gamma;F_p)
```

shows that the extension is invertible on the Frattini quotient.  The
Burnside basis argument makes it surjective, and Hopficity of a finitely
generated profinite group makes it injective.  Hence all extensions are
automorphisms.

The finite marked quotient is now exactly the characteristic-core
construction proved in
`free-full-h1-endomorphism-common-periodization-proof.md`: choose open normal
`U` omitting `y`, intersect all open subgroups of index at most `[P:U]`, and
put `Q=P/C`.  Then `Q` is a finite `p`-group detecting `y`, while every
endomorphism descends to an automorphism of `Q`.  The multiple ascending HNN
presentation maps to

```text
Q rtimes <bar phi_1,...,bar phi_r>.
```

## Source check

Checked 2026-08-30.  The residual-`p` input is K. W. Gruenberg, *Residual
Properties of Infinite Soluble Groups*, Proc. London Math. Soc. (3) 7 (1957),
29--62, DOI `10.1112/plms/s3-7.1.29`.  A modern source restates the exact
special case as Theorem 3.1(a): a finitely generated torsion-free nilpotent
group is residually `p` for every prime.  The full-Hirsch-length criterion is
also stated explicitly as Lemma 1.17 in the nilpotent-group reference audited
with this route.  The argument above records why both hypotheses apply to the
endomorphism images at hand.
