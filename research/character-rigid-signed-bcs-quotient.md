---
rg: 2
id: character-rigid-signed-bcs-quotient
kind: claim
title: Put a non-CE BCS quotient in a finite-dimension-free character-rigid signed sector
distinct_from:
  same-context-s3-endpoint-atlas: that seeks matrix-only multiplicity curvature from three local packet comparisons; this may use an algebraic quotient because sector character rigidity supplies the missing canonical-trace promotion globally.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that embeds the BCS algebra into a positive canonical corner, so pulling the corner trace back is automatic; this uses a quotient in the reverse direction and therefore needs character rigidity to identify its source trace.
---

Construct a finitely presented group `Gamma`, a finite normal subgroup
`K`, a `Gamma`-invariant irreducible type `rho in Irr(K)` with central block
projection `q=z_rho`, and a unital surjection

```text
q C^*(Gamma) q -> B,                                  (CRQ1)
```

where `B` is one fixed finite BCS algebra with a **unique** tracial state,
and that state is not Connes embeddable, such that:

1. no finite-dimensional representation of `Gamma` contains `rho` on `K`;
2. every extremal normalized character of `Gamma` supported on `q` is either
   finite-dimensional or the canonical `q`-regular character.

Then the signed corner has unique trace, and
`unique-trace-signed-corner-quotient-forces-nonhyperlinear` proves that
`Gamma` is nonhyperlinear.

The uniqueness requirement on `B` is necessary, not an optional
strengthening.  If `A=qC^*(Gamma)q` has unique trace `tau_q` and
`Phi:A->B` is unital and onto, then for any two traces `sigma_1,sigma_2` on
`B`,

```text
sigma_1 Phi=tau_q=sigma_2 Phi.
```

Surjectivity gives `sigma_1=sigma_2`.  Thus any quotient in `(CRQ1)` is
automatically monotracial.  The established input
`mipstar-bcs-tracial-nonru-exists` supplies a finite BCS algebra with at least
one trace and no Connes-embeddable trace, but it does **not** supply
monotraciality.  Before the signed quotient can be built, one must therefore
either produce a finite unique-trace non-CE BCS algebra or a finite BCS
quotient retaining non-CE while making the trace unique.

## Exact signed-sector face audit

Conditions 1 and 2 do give the claimed uniqueness once the objects exist.
Traces on `qC^*(Gamma)q` correspond to normalized characters supported on
`q`, and their extreme points are the extremal such characters.  Condition 2
says each extreme point is canonical or finite-dimensional.  Condition 1
removes the latter: a finite-dimensional corner representation with unit
`q` is exactly a finite-dimensional representation of `Gamma` whose
restriction to `K` contains `rho`.  Hence the canonical `q`-regular trace is
the only extreme point and therefore the only trace.

This also excludes every **exact** finite-dimensional representation of the
signed corner.  It is not by itself a quantitative whole-face exclusion for
approximate matrix states: hyperlinear microstates need not be close to exact
finite-dimensional representations.  The non-Connes-embeddable quotient is
what excludes those approximate states.  Indeed any trace `sigma` on `B`
pulls back to `tau_q`; surjectivity identifies their GNS von Neumann
algebras, so Connes embeddability of the canonical signed corner would make
`sigma` Connes embeddable.  Character rigidity and exact finite-dimensional
type exclusion cannot replace this quotient step.

There is also an exact direction-of-map test for `(CRQ1)`.  Since `q` is
central, every `qg` is a unitary in the corner with unit `q`.  Therefore a
unital surjection `Phi` is equivalent to a unitary representation

```text
u:Gamma -> U(B),        u_g=Phi(qg),                   (CRQ2)
```

such that the integrated representation sends `q` to `1_B` and
`C^*(u(Gamma))=B`.  The first condition says that `u|K` is entirely
`rho`-isotypic; the second is exactly surjectivity.  Conversely any such
generating representation integrates to `(CRQ1)`.

Thus placing BCS projections or Hecke operators **inside**
`qC^*(Gamma)q` proves a map in the opposite direction and does not construct
this quotient.  The missing signed-quotient theorem is a generating
`rho`-sector representation of the character-rigid group in the BCS algebra,
compatible with its finite presentation.  It must be installed without
creating a new extremal sector character of `Gamma`.

This target separates the two construction jobs cleanly.  The quotient in
`(CRQ1)` is weaker than the signed-Hecke **embedding** target: local BCS
generators may be images of corner operators and no algebraic injectivity is
needed.  Character rigidity supplies the trace promotion which a general
quotient lacks.  Conversely character rigidity without `(CRQ1)` has no
reason to place a non-CE trace in the selected sector.

Promising inputs are a higher-rank character-rigid group or lattice together
with a finite central extension whose marked type is absent from every
finite-dimensional representation.  The unresolved operation is to install
the BCS quotient without destroying that sector character classification.

There is now a sharper presentation-level restriction.  By
`central-character-rigid-sector-forbids-relator-quotients`, if the selected
central character is faithful, every tracial quotient representation of the
unique sector is faithful modulo the selected center.  In particular the
BCS quotient cannot be installed by adding any nontrivial group relator to
the character-rigid presentation.  For the explicit faithful full-central
character of Deligne's triple cover, the source trace is already unique, so
this rules out the most direct quotient-presentation compiler.  Any surviving
map must be a genuinely analytic C-star quotient with ideal inside the
full-to-reduced GNS kernel.

There is now a sharp fence on the finite-normal-subgroup version of this
proposal.  By
`finite-normal-type-corner-is-twisted-group-algebra`, the
entire invariant `rho`-corner is already

```text
M_(dim rho)(C) tensor C*_omega(Gamma/K)
```

for a finite-valued Clifford cocycle, with canonical trace equal to matrix
trace times twisted regular trace.  Therefore
`finite-normal-signed-bcs-quotient-collapses-to-twisted-factor` shows that a
successful unique-trace non-CE quotient has already produced a non-CE twisted
group factor and hence a nonhyperlinear finite central extension.  The BCS
quotient is not a weaker compiler in this setting.  Escaping this fence would
require a signed projection not arising from one invariant irreducible type
of a finite normal subgroup, or an independently new twisted-factor source.

## Exact monotracial-quotient reduction

The available MIP* BCS source is stronger in one useful direction: it has a
tracial state but **no** Connes-embeddable tracial state.  Let its universal
algebra be `B`.  If `I` is any closed ideal such that `Q=B/I` has a tracial
state, then no trace on `Q` is Connes embeddable.  Indeed, a Connes-embeddable
trace `sigma` on `Q` would pull back along the quotient map to the
Connes-embeddable trace `sigma after pi` on `B`, a contradiction.

Consequently preservation of non-CE is automatic for tracial quotients.  The
finite source problem is exactly:

> Find an ideal `I`, generated by finitely many additional BCS relations,
> for which
>
> ```text
> {tau in T(B): tau(I)=0}                               (CRQ3)
> ```
>
> is a singleton.

The displayed set is the closed face of traces which factor through `B/I`.
Thus `(CRQ3)` is necessary and sufficient for a finite monotracial non-CE
BCS quotient.  No separate non-embeddability argument is then required.

There is a qualitative but non-finite monotracialization.  Choose an extreme
trace `tau in T(B)`.  It is non-CE, and its GNS von Neumann algebra

```text
M_tau=pi_tau(B)''
```

is a finite factor and hence has its canonical trace as its unique tracial
state.  This does not solve `(CRQ3)`.  The norm-closed image
`pi_tau(B)=B/ker(pi_tau)` is separable and finitely generated, but extremality
of `tau` only makes its GNS closure a factor; it does not make `tau` the only
trace on the norm-closed image.  Passing onward to `M_tau` uses weak closure,
not a C-star quotient by finitely many BCS relations.  Moreover an
infinite-dimensional von Neumann algebra is nonseparable in operator norm,
whereas every finite BCS algebra is norm separable.  Hence the factor itself
cannot be the requested finite BCS algebra.

## Standard finite gadgets preserve trace multiplicity

Several tempting explicit constructions provably do not produce `(CRQ3)`.

- Matrix amplification does nothing: normalized corner restriction gives an
  affine bijection `T(M_n(B))=T(B)`.
- A full unital free product cannot remove traces.  Fix any trace on the
  other factor.  For every `tau in T(B)`, the reduced free-product
  construction gives a tracial state on the full free product restricting to
  `tau`; hence distinct traces of `B` remain distinct upstairs.
- Permuting finitely many copies does not help.  In
  `D=B direct-sum ... direct-sum B`, each `tau in T(B)` gives the invariant
  diagonal-average trace.  For a finite permutation action, composing that
  trace with the canonical conditional expectation gives a trace on the
  crossed product.  Distinct `tau` give distinct restrictions to `D`.
- More generally, a unique-trace algebra cannot surject onto a genuinely
  multitracial `B`, as already observed above.  Therefore an upstream finite
  monotracializer retaining `B` as a quotient is impossible.

These arguments cover the usual finite-copy, matrix, free-product, and
symmetry gadgets.  A successful finite construction must instead cut down
the trace simplex by new relations, producing the singleton face `(CRQ3)`,
or begin with a BCS whose trace is independently proved unique.  The MIP*
existence theorem and the robust BCS energy gap provide no information that
selects such a face.

## Attempts

- Start from a higher-rank lattice with the regular-versus-finite-dimensional
  character dichotomy and pass to a finite central extension whose selected
  type is killed by every finite-dimensional representation.  This supplies
  trace uniqueness but no map onto the BCS algebra.
- The available MIP*=RE BCS source is not known here to be monotracial.  Since
  every quotient of the proposed unique-trace corner must be monotracial,
  using that source requires a new finite unique-trace BCS reduction before
  any Hecke or group-corner construction begins.  Equation `(CRQ3)` is the
  exact trace-face formulation; non-CE would survive such a quotient
  automatically.
- Start from the signed-Hecke predicate packets, where a quotient onto each
  local context block is explicit.  Ordinary finite amalgamation can glue the
  local blocks only along amenable edges and remains hyperlinear; equivalently
  it cannot preserve the required global BCS quotient.  Adding those packet
  vertices to a rigid lattice also gives no known permanence theorem for the
  lattice's character classification.
- The next concrete test is whether a known character-rigid central extension
  has a generating unitary representation `(CRQ2)` inside a monotracial
  non-CE BCS algebra.  A family of Hecke operators in the group corner would
  instead construct the opposite map and does not address `(CRQ1)`.
  The representation must moreover be faithful modulo the marked center;
  quotienting the group presentation cannot create it.
- `standard-character-envelopes-do-not-supply-signed-bcs-quotient` audits
  the standard alternatives.  CDI's property-T envelope deliberately has a
  nonregular infinite-dimensional character and hence lacks the required
  dichotomy; ordinary wreath envelopes retain quotient traces; and Thompson
  `V` has a regular/trivial segment while all central extensions split.
- Compiling the BCS algebra as the coefficient ring of an elementary group
  does not supply `(CRQ2)`: by
  `elementary-bcs-canonical-unitary-compiler-fence`, nontrivial elementary
  root matrices are not unitaries in `M_n(B)`.  An abstract unitary
  representation with the required generating image would need a new
  factorial-character theorem over the noncommutative BCS ring; the published
  commutative-Noetherian and arithmetic theorems do not apply.
