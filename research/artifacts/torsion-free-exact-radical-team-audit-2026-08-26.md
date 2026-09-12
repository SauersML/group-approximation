# Torsion-free exact MF radical over `Z`: parallel construction audit

Date: 2026-08-26

## Requested endpoint

The target is a finitely presented torsion-free sofic group `G` with a
nontrivial normal property-`(T)` subgroup `K` such that

```text
Rad_MF(G)=K,                 G/K ~= Z.
```

Because every extension by `Z` splits after choosing a lift of `1`, every
candidate has the form `G=K semidirectProduct_phi Z`.  Property `(T)` makes
`K` finitely generated.  These two elementary facts make the finite-residual
obstruction below universal for the target.

## New universal obstruction

For every finitely generated group `K` and every automorphism `phi`, the
strongest form proved in the audit is

```text
R_fin(K semidirectProduct_phi Z) = R_fin(K) x {0},
Rad_MF(K semidirectProduct_phi Z) <= R_fin(K) x {0}.     (A1)
```

Here `R_fin(K)` is the intersection of the kernels of all finite quotients.
It is characteristic, and `K/R_fin(K)` is finitely generated and residually
finite.  Thus `phi` descends and gives a quotient

```text
K semidirectProduct_phi Z
  -> (K/R_fin(K)) semidirectProduct_bar(phi) Z.          (A2)
```

The target of `(A2)` is residually finite by the characteristic-finite-quotient
proof in `finitely-generated-rf-automorphism-mapping-torus-is-rf`; hence it is
MF.  This puts the finite residual of the source inside the kernel
`R_fin(K) x {0}`.  The reverse inclusion follows because the finite residual
of any subgroup maps into the finite residual of the ambient group.  Thus the
finite residual is computed exactly.  Finally the MF radical is always
contained in the finite residual, proving `(A1)`.

Consequently an exact radical equal to `K` forces

```text
R_fin(K)=K,
```

so `K` must have no nontrivial finite quotient.  Merely asking for a
non-residually-finite kernel was far too weak.

The same proof gives a useful relative form: whenever `A normal K` is
`phi`-invariant and `K/A` is residually finite,

```text
Rad_MF(K semidirectProduct_phi Z) <= A x {0}.            (A3)
```

## Complete failure of the characteristic-zero Kida--Thom seed

The previously constructed torsion-free LEF Kazhdan seed has

```text
1 -> A=C/C_+ -> K -> Gamma_0 -> 1,
A ~= directSum_(n<0) Z t^n,
```

where `Gamma_0` is a nontrivial finitely generated residually finite linear
group.  In fact `A=Z(K)`.  To see this, write

```text
Gamma = EL_3(Z[t,t^(-1)]) semidirect
        (Z[t,t^(-1)]^(3*) directSum Z[t,t^(-1)]^3).
```

If `(h,w)` centralizes the finite-index subgroup `Gamma_0`, it centralizes a
finite-index subgroup of the translation module.  Torsion-freeness of that
module forces `h` to act identically, hence `h=1`.  The projection of
`Gamma_0` has finite index in `EL_3`; a positive power of every elementary
matrix `e_ij(1)` lies in it.  Fixing all those powers forces both components
of `w` to vanish.  Therefore `Z(Gamma_0)=1`, and the central kernel in `K` is
the whole centre.

The centre is characteristic, so `(A3)` gives, for every automorphism,

```text
Rad_MF(K semidirectProduct_phi Z) <= Z(K) < K.           (A4)
```

This rules out every automorphism of the seed, not merely the noninvertible
Laurent shift.  Products, finite-index refinements, central products and
fiber products which preserve a nontrivial residually finite quotient fail
for the same reason.

## Companion-parabolic calculation

The most promising attempted repair replaced the one-dimensional central
tail by `R^m/S^m`, with `R=Z[t,t^(-1)]`, `S=Z[t]`, and used

```text
D=diag(qP,I_3,q),          P in GL_m(S), q=t^d.
```

Conjugation gives the honest automorphism

```text
U |-> qPU,       h |-> h,       v |-> q^(-1)v,       c |-> Pc,
```

and strictly compresses the natural affine Kazhdan subgroup.  Nevertheless,
an explicit centralizer calculation proves that its intrinsic compression
defect is trivial.  If `x s^n` centralizes the row lattice, then over `Q(t)`

```text
q^n P^n u h_x^(-1)=u.
```

The determinant has Laurent valuation proportional to `n`, forcing `n=0`;
the elementary matrices then force `x` into the surviving centre.  All
permitted roots and transports are central, so the natural defect set and its
normal closure are trivial.

There is also a core-independent fence.  Quotienting the mapping torus by its
central tail gives a faithful finite-dimensional affine representation over
`Q(t)`.  The machine-checked finite-dimensional sterility theorem therefore
puts the defect of every possible compression core inside the proper central
tail.  Changing the Kazhdan subgroup or root cannot make the defect fill `K`.

One positive algebraic calculation survives.  For

```text
P = [[t,-1],[1,0]],             P + P^(-1) = t I_2,
```

the module `S^2` is cyclic over `Z[P,P^(-1)]`.  Hence a single stable-orbit
relation kills the entire positive central lattice.  This resolves the
infinite central-relator problem for that near-miss, but the finite-residual
and defect fences make it unusable for the requested radical.

## Other assembly routes checked

* Direct products and finite-index fiber products retain visible finite
  quotients.
* Central products and companion matrices modify only the central tail and
  remain central-by-residually-finite.
* Inverse-limit automorphizations create infinitely generated central kernels
  and lose finite generation/property `(T)`.
* If an HNN kernel is a strict ascending union of Kazhdan cores, property
  `(T)` makes that kernel finitely generated, so the union stabilizes and the
  strict compression disappears.
* Permutational/augmentation lamp kernels have infinite support.  The relative
  property-`(T)` criterion for permutational wreath products confines a
  relative-`(T)` lamp subgroup to finitely many coordinates, so this cannot
  provide the required normal Kazhdan kernel.

## Surviving candidates

No unconditional candidate presently supplies all required seed properties.

1. The Titz Mite--Witzel finite residuals are finitely presented,
   torsion-free, simple and Kazhdan, hence have no finite quotients.  Their
   soficity is unknown, but their MF status is settled: Dadarlat's
   MF-to-weak-quasidiagonality implication and Ozawa--Thom Proposition 3.19
   show that every infinite simple Kazhdan group is non-MF and has full MF
   radical.  Building rigidity computes their
   outer automorphism group orders divide `2,32,32,64,64`, so every cyclic
   mapping torus is virtually a direct product.  These kernels solve the
   target if and only if one of them is sofic.  For the smallest kernel this
   is the explicit 15-permutation, 24-relator, one-word gate recorded in
   `titz-witzel-soficity-is-one-finite-csp`.
2. The audited Hull--Osin routed arithmetic group is two-generated, finitely
   presented, torsion-free, Kazhdan, has full MF radical, and is normally
   generated by one defect.  Soficity is exactly its missing clause.  If it
   were sofic, its direct product with `Z` would immediately solve the target.
   This is distinct from the routed Fournier--Facio quotient, which retains
   the hypotheses of Fournier--Facio Proposition 1.2 and is provably
   nonsofic.  Hull's arithmetic router supplies only an acylindrically
   hyperbolic quotient, finite-ball injectivity, suitability and torsion
   control; it supplies no finite permutation models or sofic permanence.
3. The unconditional simple sofic full-MF-radical envelope has no finite
   quotients, but the existing witness forces an involution, and the envelope
   is only countable and is not known Kazhdan or finitely generated.  The
   universal Elek--Szabo ambient group itself has explicit involutions and is
   uncountable, hence cannot have discrete property `(T)`; its countable
   descent has no torsion or Kazhdan control.
4. The characteristic-zero Kida--Thom group is torsion-free, LEF, sofic and
   Kazhdan, but its nontrivial residually finite quotient makes it impossible
   for every automorphism.

Thus the sharply reduced positive input is

```text
K finitely generated, torsion-free, sofic, property (T),
K has no nontrivial finite quotient,
and K has either:
  (i) full MF radical, or
  (ii) a finite automorphic presentation and an extrinsic defect which
       saturates K in K semidirectProduct Z.
```

## Primary-source sweep

* M. Benli, *Indicable Groups and Endomorphic Presentations*,
  <https://arxiv.org/abs/1112.1764>, Theorem 1: an `fp` group with an `fg`
  normal subgroup and cyclic quotient gives the kernel a finite ascending
  `L`-presentation.  This describes the necessary finite data but constructs
  no Kazhdan/sofic seed.
* L. Bartholdi, *Endomorphic Presentations of Branch Groups*,
  <https://arxiv.org/abs/math/0007062>, Theorem 2.4: a finite ascending
  `L`-presentation with injective substitutions embeds in an explicitly
  finitely presented ascending HNN extension.  This is useful only after the
  correct seed and action have been found.
* V. Alekseev and A. Thom, *Centralizers of Sofic Approximations of Kazhdan
  Groups*, <https://arxiv.org/abs/2608.05362>: finite presentation plus the
  paper's LEF conclusion forces residual finiteness, and Open Problem 6.1 asks
  whether a finitely presented sofic Kazhdan non-residually-finite group
  exists.
* A. Thom, *Examples of Hyperlinear Groups without Factorization Property*,
  <https://arxiv.org/abs/0810.2180>, and Y. Kida--R. Tucker-Drob,
  <https://arxiv.org/abs/1901.08735>, supply the one-sided central Kazhdan seed
  technology, but the resulting central-by-linear geometry fails `(A1)`.
* Y. de Cornulier, *Finitely Presentable, Non-Hopfian Groups with Property
  (T) and Infinite Outer Automorphism Group*,
  <https://arxiv.org/abs/math/0502140>: the non-Hopfian maps are noninjective
  endomorphisms, its central quotient introduces torsion, and the required
  soficity is not established.
* Y. Cornulier, *A Sofic Group Away from Amenable Groups*,
  <https://arxiv.org/abs/0906.3374>, and A. Kar--N. Nikolov,
  <https://arxiv.org/abs/1405.1620>, give finitely presented sofic non-LEA
  phenomena but no normal Kazhdan kernel with cyclic quotient.
* T. Titz Mite--S. Witzel, *Non-residually finite C-tilde-2 lattices*,
  arXiv:2509.05054v2, provides the torsion-free simple Kazhdan candidates; no
  soficity theorem is presently known.
* M. Dadarlat, *Obstructions to matricial stability of discrete groups and
  almost flat K-theory*, arXiv:2007.12655v2, page 2 and Proposition 3.19
  (Ozawa--Thom): MF implies weak quasidiagonality, while an infinite weakly
  quasidiagonal Kazhdan group has an infinite residually finite quotient.
  This proves the Titz--Witzel simple kernels non-MF unconditionally.
* M. Hull, *Small cancellation in acylindrically hyperbolic groups*,
  <https://arxiv.org/abs/1308.4345>, Theorem 7.1: the routing quotient protects
  a prescribed finite ball and controls suitability and torsion, but gives no
  embedding or approximation-permanence statement.  Enlarging the protected
  ball changes the quotient and therefore does not approximate one fixed
  output group.
* G. Elek--E. Szabo, *Hyperlinearity, essentially free actions and
  L2-invariants. The sofic property*, <https://arxiv.org/abs/math/0408400>,
  Proposition 2.3, Theorem 1 and Corollary 3.1: the universal simple sofic
  ambient has arbitrary cycle profiles, while the countable simple descent
  provides no torsion or Kazhdan control.

No primary source or existing Cairn node located in this audit closes the
reduced seed requirement.
