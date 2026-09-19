# The classical `SL_3(Z)` presentation closes the paper-level property-(T) gate

> **Historical route audit.** The current literal proof uses the exact P13
> certificate and checked quotient bridge, so this older semantic-presentation
> shortcut is not a release dependency or a current status report.

## Conclusion

The shortcut is valid at the level of ordinary mathematics:

```text
Rotation ~= SL_3(Z)
  => HasKazhdanPropertyT Rotation
  => HasKazhdanPropertyT Base.
```

The first implication is the exact matrix-labelled
Conder--Robertson--Williams presentation recorded by
Conder--Liversidge--Vsemirnov.  The second is classical property `(T)` of
`SL_3(Z)`.  The third is the intrinsic affine bridge already proved in
`LiteralBasePropertyTBridge.lean`.  Thus the rational `P13` Hodge certificate
is unnecessary for a paper proof of property `(T)` of the literal base.

The cited route is not used as a Lean axiom.  The current kernel proof instead
supplies an exact staged rational P13 Hodge certificate, transports it through
the checked P13-to-rotation quotient, and applies the intrinsic affine bridge.
That closes the premise-free property-`(T)` input independently of the
literature identification.

This note isolates the two external inputs behind the literal affine base in
`non_mf_groups_exist.tex`: its finite presentation and property (T).  It also
records the proof shape needed for a premise-free formal identification of the
twenty-relator group with `Z^3 ⋊ SL_3(Z)`.

## Matrix-labelled presentation

The eight relations printed in the manuscript are the Conder--Robertson--
Williams presentation

```text
x^3 = y^3 = z^2 = (xz)^3 = (yz)^3
    = (x^-1 z x y)^2 = (y^-1 z y x)^2 = (xy)^6 = 1.
```

The current labels are correct:

```text
x = [[ 0, 1, 0], [0,  0,  1], [ 1,  0,  0]],
y = [[ 1, 0, 1], [0, -1, -1], [ 0,  1,  0]],
z = [[ 0, 1, 0], [1,  0,  0], [-1, -1, -1]].
```

Conder--Liversidge--Vsemirnov, *Generating pairs for SL(n,Z)*,
J. Algebra 662 (2025), 123--137, DOI 10.1016/j.jalgebra.2024.08.008,
records this exact matrix-labelled presentation in its Introduction and
attributes it to Conder--Robertson--Williams.  The accepted manuscript was
checked through the University of Auckland repository.  Its Section 2 also
records the order-two presentation automorphism interchanging `x` and `y`
and fixing `z`; this explains why secondary sources sometimes use the
opposite `x,y` convention without changing the relator list.

The columns give exactly the nine conjugation relations printed for the
translation generators:

```text
x: e1 |-> e3,       e2 |-> e1,       e3 |-> e2;
y: e1 |-> e1,       e2 |-> -e2+e3,   e3 |-> e1-e2;
z: e1 |-> e2-e3,    e2 |-> e1-e3,    e3 |-> -e3.
```

Thus the affine presentation has exactly twenty relators: eight base
relators, three commutativity relators, and nine action relators.

## Completeness proof for the twenty-relator presentation

Let `P` be the abstract group defined by the twenty relators, let `S` be the
abstract group defined by the eight CRW relators, and let `A = Z^3`.

1. The six displayed matrices and vectors induce a surjective homomorphism
   `Phi : P -> A ⋊ S`.
2. The three commuting elements `v1,v2,v3` induce
   `V : A -> P`, with
   `V(n1,n2,n3) = v1^n1 v2^n2 v3^n3`.
3. The base relators induce `B : S -> P` sending the abstract base generators
   to `x,y,z`.
4. For each base generator, the nine action relators and the basis
   decomposition of `A` prove
   `B(s) V(a) B(s)^-1 = V(s*a)` for every `a`.  The set of `s` satisfying
   this identity for all `a` is a subgroup of `S`; since it contains
   `x,y,z`, the covariance identity holds for every `s`.
5. Define `Psi(a,s) = V(a) B(s)`.  Covariance gives
   `Psi(a,s) Psi(b,t) = Psi(a+s*b, st)`, so `Psi : A ⋊ S -> P` is a
   homomorphism.
6. `Phi ∘ Psi` is the identity by the definitions of `V` and `B`.
   `Psi ∘ Phi` fixes all six presentation generators, hence is the identity
   by presentation induction.  Therefore `P` is isomorphic to `A ⋊ S`.

This normal-form/inverse argument is preferable to an informal appeal to
“reading off the columns”: it makes surjectivity, covariance, and absence of
extra relations explicit.  It is also the direct proof shape to reproduce in
Lean.

## Property (T)

Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Example 1.7.4(i),
states exactly that `SL_n(Z)` and `SL_n(Z) ⋉ Z^n` have property (T) for
`n >= 3`.  Their proof uses:

- Theorem 1.4.15 and Corollary 1.4.16 for property (T) of the ambient Lie
  groups `SL_n(R)` and `SL_n(R) ⋉ R^n`;
- Theorem 1.7.1, which transfers property (T) between a locally compact group
  and a lattice.

Consequently the manuscript's claim for `Z^3 ⋊ SL_3(Z)` is correctly cited.
No separate finite-index or relative-property argument is needed.

## Premise-free formalization gap: closed

The exact staged P13 Hodge certificate supplies the internal finite Kazhdan
certificate, the checked rotation quotient transports it to the literal
rotation presentation, and the intrinsic bridge proves property (T) of the
literal affine base.  No literature theorem is introduced as an axiom, and
`LiteralNonMFEndpoint.manuscriptTheoremA` has no caller premise.

Direct matrix evaluation alone proves only that the matrices satisfy the eight
relations; it does not prove presentation completeness.  The staged
certificate route deliberately avoids making that incomplete calculation the
formal bridge: property `(T)` is transferred by checked quotient maps and the
intrinsic fixed-point theorem, which is enough for the premise-free endpoint.

The original CRW article was blocked by AMS/JSTOR anti-bot responses during
this pass.  The exact presentation was nevertheless checked in the open
accepted manuscript of the 2025 paper by Conder and coauthors, one of whom is
the first author of CRW.  The BHV book was checked from its complete freely
available PDF.

## Kernel-side reduction obtained in the literal presentation

The presentation-theoretic part of the affine normal form is now internal.
Writing `P` for the twenty-relator group, `S` for the eight-relator rotation
group, `T` for the subgroup generated by `v1,v2,v3`, and `R` for the subgroup
generated by `x,y,z`, the checked development proves

```text
T normal in P,       T intersection R = 1,
P = T R,             S ~= R,
P ~= T semidirect S.
```

In particular, no CRW completeness claim is used to obtain the semidirect
decomposition.  What is not yet proved is that `S` is the displayed matrix
group, or that the abelian group `T` is the full lattice rather than a
quotient of it.  (The latter can be proved independently by evaluating
`v1^a v2^b v3^c` in the affine matrix quotient.)

## Short transvection words and the next finite proof obligation

An exact integer-matrix breadth-first search found the following especially
short words for the six elementary transvections.  Upper-case letters denote
inverses:

```text
e12 = Y x z Y X        e13 = x z Y X Y
e21 = Y x y x z        e23 = X Y x z Y
e31 = x Y x z Y x      e32 = X z Y X Y X.
```

Each displayed equality has been checked by exact `3 x 3` integer matrix
multiplication; no floating-point computation is involved.  This check is
only a matrix-side fact.  It does **not** prove the corresponding equality in
the abstract eight-relator group, because that would silently assume the
very presentation-completeness theorem at issue.

These words give a finite, presentation-only route which avoids first proving
an isomorphism with all of `SL_3(Z)`.  Let `P13` be the six-generator group
with the thirteen relators used by `experiments/sl3_degree_one_spectrum.py`:
six Steinberg commutator relations, six displayed commuting-root commutator relations,
and `(e12 e21^-1 e12)^4=1`.  It is enough to prove the following three finite
lemmas, by explicit products of conjugates of defining relators:

1. substituting the six words above makes all thirteen `P13` relators trivial
   in `S`;
2. `x`, `y`, and `z` belong to the subgroup generated by those six words;
3. every matrix-word identification used when forming the rational Hodge
   certificate is witnessed by the thirteen abstract relators.

The first two lemmas give a surjection `P13 -> S`.  The third allows the exact
rational Hodge certificate to be replayed in `P13`, rather than in a data
structure which identifies words merely because their matrices agree.
Property `(T)` would then pass from `P13` to `S` by the already checked
quotient theorem.

Property `(T)` of the rotation presentation now *does* suffice for property
`(T)` of the affine group `P`.  The internal theorem
`base_hasKazhdanPropertyT_of_rotation` proves this directly from the twenty
printed relators.  After projection to the rotation-fixed subspace, every
translation has uniformly bounded displacement by the two-conjugate
translation normal form; the Hilbert-space bounded-orbit fixed-point theorem
then produces a vector fixed by translations and rotations.  Thus no
external relative-property-`(T)` input and no separate affine SOS certificate
is needed.  The remaining property-`(T)` obligation is exactly the abstract
eight-relator rotation group.

## Why the existing characteristic-two theorem is not a shortcut

The internally proved elementary-group theorem in this repository concerns
finite-type algebras over finite fields (with a separate characteristic-two
implementation).  Its proof obtains the root-set gap from a common positive
bounded exponent for every root element.  Integral root subgroups are copies
of `Z` and have no such exponent.  Moreover, a unital coefficient-ring
quotient from a positive-characteristic algebra to `Z` cannot exist.  Thus
the standard functorial descent implemented there cannot produce either
`SL_3(Z)` or `Z^3 semidirect SL_3(Z)`.  Reusing that theorem here would require
a genuinely new abstract group quotient, not a change of coefficient ring;
no such quotient has been constructed.

## The translation subgroup is not an additional completeness gap

There is a useful correction to the boundary stated above.  Once the exact
affine matrix evaluation is available, freeness of the translation subgroup
does **not** require CRW completeness.  The homomorphism

```text
(a,b,c) |-> v1^a v2^b v3^c
```

from `Z^3` onto `T` is well-defined and surjective because the three `vi`
commute and generate `T`.  If its value is one, applying the already-defined
affine quotient gives the translation matrix with last column `(a,b,c,1)`;
entrywise equality with the identity forces `a=b=c=0`.  Thus the map is
injective.  Consequently `T ~= Z^3` can be formalized independently of the
rotation presentation.

This sharpens both remaining obligations: the only presentation-completeness
problem is the rotation factor, and the internal bounded-orbit argument has
reduced affine property `(T)` to property `(T)` of that same rotation group.

The unsuccessful Knuth--Bendix trial is also informative.  SymPy's completion
of the eight-relator presentation did not terminate within a short bounded
MSI run and was stopped; the initial 53-rule reducer did not close even the
six substituted Steinberg relators.  Therefore a bare normal-form call is not
currently a proof-producing route.  The next implementation target is the
finite relator-replay lemma in item 1 above, with every rewrite recorded and
checked, rather than a longer untrusted completion run.
