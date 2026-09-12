# The hyperlinear-to-MF saturation compiler

## General router--detector theorem, torsion-free full-radical output, and finite challenge certificate

**Date:** 2026-08-22

## Executive theorem

Let `E` be countable and let `D <= E` be a subgroup killed in the normalized
Hilbert--Schmidt ultraproduct shadow of every operator-norm almost
representation of `E`.  Then every normal property-`(T)` subgroup contained
in `D` lies in the operator-MF residual of `E`.

If a quotient map `q : E -> Q` routes `D` over a normal Kazhdan subgroup
`K triangleleft Q`, then `K` lies in the MF residual of `Q`.  In particular,

```text
q(D) = Q  and  Q has property (T)
  ==> normMFResidual Q = Q.
```

Once a group has full MF residual, every quotient does too.  Hence every
nontrivial quotient is non-MF and every homomorphism to an operator-MF group
is trivial.

The architecture is

```text
tracial / hyperlinear invisibility
  + normal-closure saturation compiler
  + Kazhdan moving-corner detector
  -> full operator-MF radical.
```

Unlike the single-compression construction, this theorem does not care how
the tracial kill was proved.  A compression-centralizer argument is one
input; a game, cocycle, projective-representation, or future hyperlinear
obstruction can be another.

## 1. Operator MF and the full residual

For matrix sizes `d_n`, let

```text
Q_op = (product_n M_(d_n)(C)) / (operator-norm-null sequences).
```

The norm-MF residual is the intersection of the kernels of all homomorphisms
into all such unitary groups.  Thus `normMFResidual G = top` means that every
norm-corona homomorphism out of `G` is trivial.  A nontrivial group with this
property is not MF.

## 2. Op-to-HS killed subgroups

An operator-norm almost representation of `E` is a sequence

```text
phi_n : E -> U(d_n)
```

whose multiplicative defect converges pointwise to zero in operator norm.
Because normalized Hilbert--Schmidt norm is bounded by operator norm, it
defines a homomorphism in every cofinite normalized-HS ultraproduct.

Call `D <= E` **op-to-HS killed** when every such hyperlinear shadow sends
every `d in D` to `1`.  This is deliberately only a tracial conclusion.
Without an additional detector, operator-norm movement may hide on a corner
whose normalized rank tends to zero.

In Lean the kill hypothesis is the quantified statement

```text
forall (B : OpAlmostRepresentation E) (U : Ultrafilter Nat)
  (hcof : U <= cofinite) (x in D),
  B.toAsymptoticUnitaryRepresentation.toUltraproductHom hcof x = 1.
```

## 3. Abstract normal-Kazhdan detector

The kernel-checked theorem

```text
KazhdanCompressionCore.normalKazhdan_le_normMFResidual_of_hyperlinear_killed
```

says that if `D` is op-to-HS killed and

```text
K triangleleft E,
K has property (T),
K <= D,
```

then

```text
K <= normMFResidual E.
```

There is no compression core in this theorem's hypotheses.  The aggregate
form is

```text
normalKazhdanPart_le_normMFResidual_of_hyperlinear_killed,
```

where `normalKazhdanPart D` is the join of all normal Kazhdan subgroups
contained in `D`.  Literal corona-kernel and weak-MF forms are proved in the
same module.

### Moving-corner proof

Assume an element of `K` survives in a norm-corona representation of `E`.
Restrict to the countable range.  The image of `K` is normal, Kazhdan, and
nontrivial.  Property `(T)` produces its fixed-space projection; take the
orthogonal moving projection.

Normality makes both spaces invariant under the whole ambient image.  After
the standard approximate invariance and polar correction, the moving corners
carry an operator-norm almost representation of the ambient group.  Normalize
trace by the moving rank, not by the original dimension.  The Kazhdan gap
then forces some fixed element of `K` to survive in normalized HS norm.

Pull the corner representation back to `E`.  Since `K <= D` and `D` is
op-to-HS killed, that same element must be trivial in the HS ultraproduct, a
contradiction.  This is the general solution to rank dilution.

The implementation is
`GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean`, built from
`InternalRadicalGap.exists_setup` and
`InternalRadicalGap.exists_ambientMovingCornerSchedule`.

## 4. Saturation compiler

Let `q : E -> Q` satisfy `q(D)=Q`, and assume `Q` has property `(T)`.
The equality makes `q` surjective, so countability of `Q` follows from
countability of `E`.  For the partial-saturation statement below, assume
`Q` countable explicitly.

First, `Q` is itself op-to-HS killed.  Given an operator-norm almost
representation `psi_n` of `Q`, precompose it with `q`.  For any `y in Q`,
choose `d in D` with `q(d)=y`.  Then

```text
psi_HS(y) = psi_HS(q(d)) = (psi o q)_HS(d) = 1.
```

Apply the abstract detector inside `Q` with killed subgroup `Q` and normal
Kazhdan subgroup `K=Q`.  It follows that

```text
normMFResidual Q = top.
```

This proves the full saturation theorem.

### Partial saturation

The same pullback argument shows that `q(D)` is op-to-HS killed even when it
is proper.  Therefore any

```text
K triangleleft Q,
K != 1,
K has property (T),
K <= q(D)
```

lies in `normMFResidual Q`, and `Q` is non-MF.  Equivalently,

```text
normalKazhdanPart (q(D)) <= normMFResidual Q.
```

This is the most reusable form: the compiler only has to route the tracially
invisible subsystem over one nontrivial normal Kazhdan subsystem.

## 5. Quotient heredity and MF-target orthogonality

If `normMFResidual Q = top` and `r : Q ->> L`, every norm-corona
representation of `L` pulls back to a trivial representation of `Q` and is
therefore itself trivial.  Thus

```text
normMFResidual L = top.
```

This is kernel-checked as the corona and norm forms

```text
coronaMFResidual_eq_top_of_surjective
DefectRoutingData.quotient_coronaMFResidual_eq_top
DefectRoutingData.quotient_normMFResidual_eq_top.
```

If `f : Q -> M` and `M` is operator MF, then `f(Q)` is both a quotient of
`Q` and a subgroup of an MF group.  It has full residual by quotient heredity
and is MF by subgroup heredity, so it is trivial.  The routed interface proves
this directly as

```text
DefectRoutingData.hom_eq_one_to_isOperatorMF.
```

Finite, finite-dimensional unitary, and countable residually finite targets
are immediate special cases.  In particular the output has no nontrivial
finite quotient or proper finite-index subgroup.

## 6. Acylindrical small-cancellation compiler

Suppose now that `E` is finitely presented, torsion-free, acylindrically
hyperbolic, and has property `(T)`, and that
`1 != D triangleleft E` is op-to-HS killed.

Torsion-freeness makes `D` infinite.  Normality makes it `s`-normal, so
Osin's theorem makes its action non-elementary; the finite-radical clause of
Hull suitability is vacuous.  Choose noncommensurable loxodromics
`h_1,h_2 in D` whose generated subgroup `S_0` is suitable.

For a finite generating set `t_1,...,t_m` of `E`, apply Hull's Theorem 7.1
with the `t_i` as prescribed elements.  It gives a quotient `q:E->>Q` with

```text
q(t_i) in q(S_0) for every i.
```

Consequently

```text
Q = q(S_0) = q(D),
```

and `Q` is generated by `q(h_1),q(h_2)`.  Choose the injectivity radius to
protect a fixed `1 != d_0 in D`; then `Q != 1`.  Hull's clauses preserve
acylindrical hyperbolicity and torsion-freeness.  Only finitely many relators
are added, so finite presentation survives.  Property `(T)` passes through
`E ->> Q`.

The saturation theorem now gives full MF residual, and quotient heredity gives
the same conclusion for every quotient.  Hence:

> Every finitely presented torsion-free acylindrically hyperbolic Kazhdan
> group with a nonzero normal op-to-HS killed subgroup has a nontrivial
> 2-generated finitely presented torsion-free acylindrically hyperbolic
> Kazhdan quotient with full MF residual, all of whose nontrivial quotients
> again have full MF residual.

The small-cancellation input is the established Cairn node
`common-quotient-onto-normal-subgroup`, whose proof and source audit are in
`notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md`.  This remains the
paper-level, non-Lean trust boundary.

## 7. Explicit Fournier--Facio input

The published construction supplies a finitely presented torsion-free
acylindrically hyperbolic property-`(T)` group `G_0` with

```text
Gamma = pi(P),
t = pi(u_1),
S' = pi(S),
J = t^(-1) S' t,
[Gamma,J] = 1,
t J t^(-1) = S' <= Gamma.
```

Choose `1 != c in J` and put `s=tct^(-1) in S'`.  Its compression defect is

```text
D_0 = normalClosure({[s,gamma] : gamma in Gamma}).
```

Every displayed commutator lies in `normalClosure(S')`, giving one
containment.  Since `S'` is nonabelian simple and `s != 1`, some
`x in S' <= Gamma` has `[s,x] != 1`.  Thus `D_0 cap S'` is a nontrivial normal
subgroup of `S'`, so `S' <= D_0`.  Therefore

```text
D_0 = normalClosure(S').
```

The compression theorem proves `D_0` op-to-HS killed.  This concrete kill is
registered as

```text
KazhdanCompressionCore.defectNormal_hyperlinear_killed,
```

while the simple-subgroup saturation is

```text
FournierFacioDefectData.simpleSubgroup_le_defectNormal.
```

Applying one further Hull routing pass to `(G_0,D_0)` gives a group `Q` that
is 2-generated, finitely presented, torsion-free, acylindrically hyperbolic,
Kazhdan, and satisfies

```text
normMFResidual Q = top.
```

Every nontrivial quotient of `Q` has the same full-radical property.  This is
the abstract explanation of the existing explicit node
`defect-saturation-full-mf-radical`.

## 8. Finite marked-group challenge

Let the 2-generated output have a finite presentation

```text
Q = <x_1,x_2 | R>
```

and choose a word `v` that is nontrivial in `Q`.  Consider all 2-marked groups
whose marked generators satisfy every relation in `R` and satisfy `v != 1`.

The relations give a surjection `Q ->> L`; the inequation makes `L`
nontrivial.  Quotient heredity gives

```text
normMFResidual L = top.
```

Because `R` is finite and `v` is one word, these are finitely many cylinder
conditions in marked-group space.  The resulting set is nonempty, clopen, and
consists entirely of full-radical non-MF groups.

Thus the compiler emits a finite challenge certificate

```text
(R ; v != 1).
```

Arbitrary relations may be added afterward: either they kill `v`, or the new
quotient remains in the certified full-radical class.  The obstruction is
self-hardening under quotient post-processing.

## 9. Research-program consequence

The reverse-Kleene route asked for a uniform, dimension-independent
operator-norm collapse estimate.  The saturation compiler changes the search
target:

```text
find any nonzero normal subgroup D already killed by hyperlinear analysis
  -> route every generator through D
  -> q(D)=Q
  -> extract any surviving moving corner by property (T)
  -> full MF radical.
```

The source of the kill may be a game compiler, cocycle obstruction,
projective-representation obstruction, compression-centralizer theorem, or a
future nonhyperlinear construction.  It need not directly solve the MF norm
problem.  The matrix problem is converted into a normal-subgroup routing
problem.

## 10. Trust boundary and Cairn map

Kernel-checked:

- arbitrary op-to-HS kill plus normal Kazhdan detector:
  `NormalKazhdanHyperlinearKilled.lean`;
- MF-radical and literal corona endpoints:
  `NormalKazhdanMFRadical.lean` and `ActualCoronaMFRadical.lean`;
- routed full radical, MF-target triviality, and quotient heredity:
  `TorsionFreeFullMFRadical.lean`;
- concrete simple-factor defect saturation:
  `FournierFacioDefectData.simpleSubgroup_le_defectNormal`.

Source-audited rather than formalized:

- Hull--Osin routing of a prescribed infinite normal subgroup onto a
  protected, torsion-free, finitely presented acylindrically hyperbolic
  quotient.

Cairn decomposes the master statement into:

```text
hyperlinear-killed-normal-kazhdan-mf-transfer
  -> hyperlinear-to-mf-saturation-compiler

hyperlinear-to-mf-saturation-compiler
AND common-quotient-onto-normal-subgroup
  -> acylindrical-hyperlinear-saturation-compiler

acylindrical-hyperlinear-saturation-compiler
AND fournier-facio-torsion-free-skeleton
  -> defect-saturation-full-mf-radical

defect-saturation-full-mf-radical
  -> full-mf-radical-finite-challenge-cylinder.
```

This is the general theorem to reuse.  The earlier router--detector artifact
is its explicit Fournier--Facio instance.
