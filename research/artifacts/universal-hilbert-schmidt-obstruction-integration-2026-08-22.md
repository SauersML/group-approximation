# Universal Hilbert--Schmidt obstruction integration — 2026-08-22

This artifact integrates the supplied “Universal Hilbert--Schmidt
obstructions to hyperlinearity” note into the existing Cairn programme.  It
does not introduce a parallel route: most of the note's substantive results
were already present under more application-specific names.

The broader corner/Bernoulli bookkeeping remains in
`research/artifacts/universal-attack-trace-promotion-audit-2026-08-22.md`.
This file adds only the exact `kappa_Gamma`/minimax formulation, the reusable
finite-defect ultraproduct theorem, and the no-go connections not explicit in
that earlier audit.

## Exact universal reduction

For a finite `E subset Gamma` containing the identity, define

```text
kappa_Gamma(E)
 = inf_(d>=1) inf_(theta:E->U(d), theta(1)=I)
   max( max_(x,y,xy in E)||theta(x)theta(y)-theta(xy)||_(2,d),
        max_(x in E\{1})|tr_d(theta(x))| ).             (UHS1)
```

The equivalence

```text
Gamma hyperlinear  <=>  kappa_Gamma(E)=0 for every finite E             (UHS2)
```

is the exact numerical form of
`nonhyperlinear-group-has-finite-canonical-microstate-witness`.  Its proof is
the exhaustion/diagonal argument in
`nonhyperlinear-finite-microstate-witness-proof`.  Thus nonhyperlinearity is
one finite packet with quantifier order

```text
exists E, c>0; for every d and every theta, defect(theta)>=c.
```

The general compactness engine is now recorded separately as
`finite-matrix-defect-zero-is-exact-ultraproduct-realizability`: a finite
unitary polynomial-and-trace defect has global infimum zero exactly when its
zero set occurs in a tracial matrix ultraproduct.  This subsumes the same
principle used in `atlas-rankwise-gap-is-ultraproduct-obstruction` and
explains the rate warning in
`dimension-kleene-threshold-needs-amplification-envelope`.  Fixed-dimension
positive gaps do not defeat an increasing-dimension diagonal schedule.

## The non-CE packet already exists

The supplied finite involutive moment theorem is exactly
`non-ce-algebras-have-finite-symmetry-moment-witnesses`, based on
`separable-finite-algebras-have-symmetry-bases`.  It gives finitely many exact
symmetries, finitely many target word moments, and one positive gap against
all matrix dimensions.  The important scope boundary is unchanged: the
target moments are arbitrary tracial scalars, not the canonical values zero
off the identity.  `projectively-closed-symmetry-bases-are-hyperfinite`
explains why the symmetry basis cannot simply be declared a projective group
basis.

## Canonical compiler theorem

The note's compiler theorem is the abstract form of
`canonical-trace-promotes-non-ce-profile`.  Fix a finite non-CE symmetry
packet with matrix gap `epsilon`.  If one finite canonical group packet of
defect `eta` decodes exact matrix symmetries whose target moment error is at
most `C eta` whenever `eta<delta_0`, then

```text
kappa_Gamma(E) >= min(delta_0,epsilon/C).                (UHS3)
```

Indeed a smaller group defect would decode a matrix tuple inside the
forbidden moment ball.  At the exact level it is enough that every
regular-trace realization of the group packet in a tracial matrix
ultraproduct produce the forbidden moment tuple; the general ultraproduct
claim then supplies the numerical constant automatically.  Cairn's concrete
route `nonhyperlinear-via-canonical-trace-promotion` fixes the non-RU BCS/RACG
source in advance, preventing the unrestricted compiler from becoming the
circular corner reformulation in
`universal-canonical-trace-promotion-is-goal-equivalent`.

## Canonicalization no-go map

| Proposed operation | Integrated Cairn result |
|---|---|
| projective-kernel extraction | `non-ce-trace-does-not-promote-to-subgroup-character-gap`; the strengthened free-product example has non-CE projectively faithful character but CE regular character |
| tensor-power washout | `character-diracization-limit` computes the regular quotient limit, while `diagonal-tensor-trace-powers-forget-full-gns-tensor` shows non-CE need not survive |
| independent free labels | `free-label-orthogonalization-erases-payload-trace` |
| entrywise modulus-squared Markovization | `dephasing-destroys-multiplicativity`; its `2 x 2` Hadamard witness is already an exact constant defect, so the circle discretization adds no stronger conclusion |
| scalar trace after diagonal normalization | `scalar-trace-of-diagonal-normalizer-is-permutation-blind` |
| local abelian/amenable diagonalization | `approximate-bernoulli-lamp-extraction-is-cartan-completion`; independently chosen multiplicity gauges leave the global coherence problem |

These are structural exclusions, not rate defects.  The positive target is
the expectation-preserving form of `invariant-cartan-completion`: place the
abelian algebra in a diagonal ultraproduct, normalize it coherently by all
relevant words, and preserve conditional expectation.  The last condition
prevents diagonal phases from simulating trace cancellation while carrying
the identity permutation.

## Net effect on the programme

The approximation quantifiers are closed: neither convergence schedules nor
dimension-dependent rounding should be optimized separately.  The remaining
work is the already-open finite canonical-trace promotion/coherence gate.
Failure of Connes embedding supplies the all-dimensions moment obstruction;
it does not supply the regular-trace transfer.  No existence claim for a
nonhyperlinear group follows until that transfer, a literal group-factor
corner realization of the fixed source, or another established Cairn route
is completed.
