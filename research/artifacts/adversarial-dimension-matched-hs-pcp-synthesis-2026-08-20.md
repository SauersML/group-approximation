# Dimension-matched adversarial computation: synthesis and backend boundary

**Date:** 2026-08-20  
**Status:** the self-reference layer is proved; the game-level fixed point is
proved; the constant-HS group-word backend remains open.  No nonhyperlinear
group is claimed.

## What is already theorem-level in Cairn

The adversarial idea no longer requires a group to inspect its own matrix
dimension.  `dimension-matched-kleene-microstate-diagonal` proves that a
machine-indexed compiler only has to defeat the one dimension printed by its
fixed-point search.  `instance-modulated-kleene-microstate-diagonal` permits
the positive defect and mark thresholds to depend computably on the source
program.  `dimension-kleene-threshold-needs-amplification-envelope` records
the sharp caveat: arbitrary thresholds learned only after halting are not
enough, because hyperlinearity supplies no error-versus-dimension rate.

At verifier level, `kleene-mipco-self-destroying-game` applies the same fixed
point to Lin's `MIP^co=coRE` compiler and obtains one finite game with a
perfect/high commuting strategy but a fixed gap against every
finite-dimensional strategy.  The adversarial program therefore already
exists at game level.  What remains is groupification.

The direct machine route has also discharged several subproblems:

- `self-referential-bcs-nonzero-signal-collapse` gives a nonzero BCS signal
  erased by all sufficiently accurate finite-dimensional strategies;
- `trace-functorial-bcs-signal-groupification-impossible` proves that a decoder
  applying to every tracial representation would contradict the regular
  trace, so the backend must be finite-dimensional-only;
- `multiplicity-pi-turing-tape` identifies the commutant multiplicity of a
  fixed finite irreducible CPU sector with the finite matrix tape;
- `two-generator-amitsur-levitzki-dimension-oracle` supplies an exact additive
  polynomial detector on that tape, but no bounded group-word/HS compiler;
- `conjugacy-compressed-dimension-trigger` proves literal conjugate addressing
  has exactly zero norm loss;
- `stabilizer-generator-control-has-unbounded-address-loss` isolates the
  remaining naming/coherence loss;
- `odd-selector-priority-decoding` removes one-hot selector enforcement from
  the LCS lowering, leaving cross-context consistency as the live issue.

## The correct backend API

For a compiler output `(G_M=<S_M|R_M>,w_M)`, the useful quantitative currency
is a finite-dimensional carrier

```text
mu_0(U)=(1/4)||w_M(U)-1||_2^2.
```

On the halting output `D`, it would suffice to prove

```text
mu_0(U) <= 2^(-N(D)) + C_M Def_(R_M)(U)^2,              (AHS1)
```

for every `D`-dimensional tuple, where `C_M` is computable before the
fixed-point search starts and is independent of `D`, runtime and virtual tape
length.  Choose `N(D)` so the first term is below a fixed constant less than
`1/2`, then choose the source-dependent search threshold so the second term
keeps `||w_M(U)-1||_2` below one fixed `alpha<sqrt(2)`.

The natural way to manufacture `(AHS1)` is the backwards recurrence

```text
mu_n <= (1/2) mu_(n+1) + C p(n) sqrt(E),                (AHS2)
```

or its squared-energy refinement.  `contractive-computation-ladder` proves
that geometric contraction makes every polynomial certificate cost summable.
It does not construct the group-word current `mu_n`.

This API must remain matrix-only.  An exact trace inequality of the same form
would apply to the group's regular representation and force the marked word
to be trivial.  Properly infinite exact completeness is permitted by
`kleene-completeness-needs-only-a-nontrivial-exact-representation`; only the
finite-dimensional soundness side must pay `(AHS1)`.

## Why character-orbit overflow is not the backend

An exact finite register can force equal multiplicities around a long
character orbit and hence exclude a chosen character in dimensions smaller
than that orbit.  The scalar cyclic implementation does not have a fixed HS
gap.  `cyclic-character-orbit-pressure-has-vanishing-hs-gap` gives the exact
one-dimensional witness: the relations `a^p=1`, `tat^(-1)=a^3` admit a root
`a` arbitrarily close to `-1` with relation defect `2 sin(pi/p)`.  Larger
capacity therefore makes the relation softer.  This sends the construction
back to the forbidden post-halting threshold regime.

The negative calculation supports the discrete-spectrum design choice:
Pauli/Clifford or Schur multiplicity pressure is quantitatively healthier than
continuous phase orbit pressure, although it still needs the missing
constant-HS group-word decoder.

## Concentrated open theorem

The remaining theorem is an invariant HS--PCP transducer: finitely many group
word prototypes must decode a virtual verifier/tape with global consistency,
rejection and signal-loss bounded by one program-dependent constant times the
global normalized-HS relator energy, independently of dimension, runtime and
the number of virtual addresses.  Perfect infinite representations must
decode perfectly.

`hs-pcp-boone-compiler` is the direct group-machine formulation.
`zpc-context-mismatch-transducer` is the perfect-game-to-LCS formulation.
`constant-hs-sound-self-detecting-tape-groupification` is the multiplicity-
tape formulation.  These are three interfaces to the same backend boundary,
not three independently solved routes.

External landmarks remain Taller--Vidick, arXiv:2507.22444, where perfect
completeness for the LCS hardness result would imply a nonhyperlinear group,
and Lin, arXiv:2510.07162, which supplies the coRE-oriented game compiler.
