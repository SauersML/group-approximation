---
rg: 2
id: atlas-left-ideal-rank-nonwandering
kind: claim
title: The augmented left relator ideal cannot wander across repeated natural chart modules
distinct_from:
  atlas-defect-orbit-span-quotient-dichotomy: that gives an exact quotient when the relator orbit-span is proper; this is the missing normalized-rank theorem asserting properness for low-rank augmented residuals.
  atlas-augmented-relator-ideal-not-left-finite: that rules out a universal finite algebraic spanning list; this asks for a representation-specific Sylvester-rank estimate despite the infinite one-sided generating width.
  atlas-augmented-rank-zero-set-compactness: that states the finite-zero promotion conclusion; this is its precise finitely presented module input.
  atlas-morita-coefficient-cyclicity-reduction: that exactly identifies the full orbit-span with a coefficient-algebra cyclic span on the multiplicity space; the present claim is the still-missing assertion that the thirteen residual formulas cannot create a sublinear cyclic seed.
---

OPEN.  Use the notation

```text
P=F2[A8*A8],
I=ker(P -> F2[Gamma_+]).
```

For every finite-dimensional left `P`-module `E` whose restriction to each
`A8` factor is the same repeated natural module `V^m`, let

```text
D_E=sum_(r in R_+) im(r-1),
I E=sum_(a in P) a D_E.                               (LRN1)
```

Prove the representation-specific nonwandering implication

```text
max_(r in R_+) rank_E(r-1)/dim(E) ->0
       implies
dim(I E)/dim(E) ->0                                   (LRN2)
```

for every sequence of such modules.  The weaker conclusion
`liminf dim(IE)/dim(E)<1` is already sufficient to extract one exact finite
quotient.

This is the surviving Sylvester-rank module statement.  It cannot follow
from finite one-sided generation: `atlas-augmented-relator-ideal-not-left-finite`
proves that `I` has infinite left generating width.  Nor can it be tested by
one fixed formal symbol: the cyclic and formal-Toeplitz promotion theorems
already close those cases.  A proof must instead find a rank inequality or
shrunk-subspace certificate special to the thirteen relations and the two
`V^m` restrictions, controlling all moving left translates at once.

An explicit countermodel would be equally decisive: construct modules
`E_n` of this marked type with `dim D_(E_n)=o(dim E_n)` but

```text
I E_n=E_n.                                             (LRN3)
```

By the fixed-width fences, such a construction must have growing state width
or genuinely nonstationary coefficient data.

## Attempts

- **Finite one-sided saturation fails algebraically.**  If finitely many
  left translates of the thirteen generators spanned `I`, their images would
  give `(LRN2)` by rank subadditivity.  The established non-left-finiteness
  theorem rules out exactly this argument.
- **Fixed symbolic finite sections specialize.**  Block-circulant,
  low-rank cyclic perturbation, and fixed formal-Toeplitz gauges all promote
  to exact finite-field points.  They cannot supply `(LRN3)`.
- **Generic cyclicity is irrelevant.**  Two conjugate matrix-algebra chart
  actions can make a rank-one subspace cyclic, but this does not arrange that
  the cyclic seed is the simultaneous image of the thirteen specific
  relator residuals.  A generic expansion argument therefore neither proves
  nor refutes `(LRN2)`.
- **Universal ideal identities are too strong.**  A fixed identity placing a
  nonzero chart marker in the two-sided relator ideal would also hold in the
  exact binary-Leavitt image, where both chart copies remain faithful.
  Any positive certificate must use finite-module rank selection rather than
  ordinary ideal membership.
- **Bass--Serre Folner compression has the wrong modular chart type.**
  `atlas-edge-folner-modules-miss-natural-type` compares one transvection:
  its normalized `rank(t-I)` is `1/2` on every free/regular edge-orbit module
  but `1/4` on `V^m`.  A vanishing-density boundary cannot pay this fixed
  gap.  Thus truncating the infinite chart-coset graph does not construct
  `(LRN3)`; a negative model needs positive-density nonfree chart cells and
  a new mechanism keeping all thirteen residual images small there.
- **Morita reduction isolates the exact growing-width enemy.**
  `atlas-morita-coefficient-cyclicity-reduction` writes the chart change as
  a `4 by 4` block matrix `T=(T_ia)` with inverse `(S_bj)`.  The full defect
  orbit is exactly `V tensor C_T U_D`, where
  `C_T=<T_ia S_bj><=M_m(F2)` and `U_D` is the multiplicity-coordinate span
  of the thirteen residual images.  Thus a countermodel is precisely a
  sequence in which `dim U_D=o(m)` but `C_T U_D=F2^m`.  This also proves
  that its alternating saturation depth is at least
  `log_16(1/(13 epsilon))` when every normalized residual rank is at most
  `epsilon`.  Generic coefficient algebras can have one-dimensional cyclic
  seeds.  In fact the cited reduction gives an explicit binary unipotent
  chart change whose coefficient algebra is `M_m(F2)`, so the
  repeated-natural chart type alone cannot close the claim;
  the remaining input must use the thirteen explicit residual formulas to
  force a proper `C_T`-invariant subspace.
