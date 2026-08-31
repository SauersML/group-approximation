---
rg: 2
id: moving-lamp-refinement-cocycle-has-diffuse-fibers
kind: claim
title: Moving lamp spectral blocks form a refinement cocycle with diffuse invisible fibers
distinct_from:
  finite-covariance-energy-sees-only-character-restrictions: that computes the off-restriction transport energy for one finite test set; this gives the exact refinement and actor-composition laws among all finite-window spectral blocks.
  elementary-abelian-regular-normalizers-have-diffuse-fibers: that settles one invariant regular window and gives the coherent Fourier countermodel; this identifies the moving-window Cech/groupoid object and proves the positive overlap-gluing lemma.
  kt-c-normalization-seam-is-a-relative-commutant-cocycle: that is a nonabelian correction equation for one arithmetic compressor normalizer; this is the inverse system of lamp-character fibers over finite coordinate windows.
artifacts:
  - notes/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md
---

**ESTABLISHED REFINEMENT/OVERLAP BOUNDARY.**  Let a group `G` act on a set
`X`, put `A=direct_sum_X C_2`, and write `B_E=direct_sum_E C_2` for a
finite window `E subset X`.  In an exact finite-dimensional lamp
representation define the character projections

```text
P_(E,chi)=2^(-|E|) sum_(b in B_E) chi(b) rho(b).         (MRC1)
```

For `E subset F`, actor covariance and refinement obey

```text
P_(E,chi)
 =sum_(psi in dual(B_F), psi|E=chi) P_(F,psi),           (MRC2)

U_g P_(E,chi) U_g^*
 =P_(gE,g chi).                                         (MRC3)
```

The partial transports

```text
u_(g,E,chi)=P_(gE,g chi) U_g P_(E,chi)                  (MRC4)
```

therefore satisfy two exact compatibility laws:

```text
u_(g,E,chi)
 =sum_(psi|E=chi) u_(g,F,psi),                          (MRC5)

u_(h,gE,g chi) u_(g,E,chi)=u_(hg,E,chi).                (MRC6)
```

Thus the moving finite windows form a strict refinement/action-groupoid
cocycle.  A change of bases inside the character fibers is its gauge action.
The coefficient groups grow under refinement: the commutant of `B_E`
contains arbitrary unitaries on every restriction fiber, and a gauge chosen
at `E` need not preserve the finer splitting at `F`.

## Positive two-window gluing lemma

There is no separate Cech obstruction at the level of lamp covariance.
Suppose `U_g` has coordinate-lamp covariance errors

```text
epsilon_x=||U_g rho(a_x) U_g^*-rho(a_(gx))||_2
```

for `x in E union F`.  Then covariance glues to every
`b in B_(E union F)` by telescoping, and every character projection of
the union satisfies

```text
||U_g P_(E union F,chi) U_g^*
       -P_(g(E union F),g chi)||_2
 <=(1/2) sum_(x in E union F) epsilon_x.                (MRC7)
```

In particular exact covariance on two overlapping windows is exact on their
union.  Overlap consistency of the spectral PVMs is automatic; it is not the
missing Kun--Thom theorem.

## Sharp overlap countermodel for metric rounding

Overlap does not control the internal fiber cocycle.  Let

```text
X=N times (Z/4),       t(r,i)=(r,i+1),
S_m={1,...,m} times (Z/4),
E_m={1,...,m} times {0,1},
F_m={1,...,m} times {1,2}.
```

On `ell^2(B_(S_m)) tensor C^(k_m)`, with `k_m -> infinity`, use the
regular lamp representation and

```text
U_(t,m)=Q_(t,m) tensor F_(k_m),                          (MRC8)
```

where `Q_(t,m)` is the canonical coordinate permutation and `F_(k_m)`
is the Fourier matrix.  Then `U_(t,m)^4=1`, all actor products, all lamp
covariances, all refinement identities, and all overlap identities for
`E_m,F_m` and every subwindow are exact.  The common overlap has `m`
coordinates and grows without bound.  Nevertheless

```text
inf_(M monomial)||U_(t,m)-M||_2^2
 >=2-2/sqrt(k_m),                                       (MRC9)
```

and the squared distance remains `2-o(1)` after arbitrary `o(d_m)`
block padding.  Tensoring the construction with separating regular
quotients of `SL_3(Z)` gives the same example with an infinite residually
finite Kazhdan actor.

This countermodel does not refute permutation transfer: `Q_(t,m) tensor 1`
is already a coherent permutation family.  It proves that neither growing
overlap nor property `(T)` forces the given refinement cocycle to have
small gauge.

## Finite-cycle sharpening

[[finite-schreier-holonomy-is-the-simultaneous-lamp-gauge-obstruction]]
now gives an exact check on one regular packet.  After gauging a spanning
tree in the finite character Schreier graph, simultaneous gauge equivalence
to any proposed target is equivalent to simultaneous unitary conjugacy of
the source and target holonomies on the fundamental chords.  The
Hilbert--Schmidt residual on each chord is exactly its holonomy-conjugacy
residual, with no path-length loss.

A multiplicity-one bent-phase model shows this obstruction is substantive:
exact canonical trace and exact covariance need not make the supplied
normalizer commutant-gauge equivalent to any permutation normalizer.  A
different permutation representative still exists, so target construction
rather than gauge trivialization remains the live issue.

## Direct-target sharpening

[[finite-lamp-targets-glue-after-action-groupoid-completion]] abandons
conjugation of the supplied normalizers.  Once a finite actor/cylinder
groupoid has actually been completed, regular isotropy carriers glue all
atom transports after an explicit orbitwise rank trim.  Fourier Parseval
bounds the normalized atom imbalance on a union window by half the square
root of the sum of squared nontrivial lamp traces.

The remaining boundary is discrete rather than perturbative.  One wrong
site relation on a regular binary-character block has Hamming cost at least
`1/2`; adding boundary coordinates does not dilute it.  Thus direct target
construction still has to extract an approximately multiplicative finite
action groupoid on almost every block.  Marginal window couplings and
overlap refinement do not supply that joint object.

## Exact surviving global seam

The open datum is a compatible **spatialization**, not overlap gluing:
choose permutation representatives, or commutant gauges which respect every
refinement, simultaneously over an exhaustion by windows that move under
several actor generators, while preserving actor products on almost every
point.  Fixed-window covariance determines the quotient labels but is
silent on the increasing multiplicity fibers.  This is precisely the
moving-window coherence still missing from equivariant normalizer transfer;
the Kun--Thom nonhyperlinearity route remains OPEN.

DERIVATION
moving-lamp-refinement-cocycle-proof
