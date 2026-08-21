---
rg: 2
id: central-word-state-face-compiler
kind: claim
title: Compile the fixed tracial non-RU BCS face into a phase-safe central-word clause face
distinct_from:
  phase-safe-toric-gap-game-exists: that asks only for the final game; this is the surviving state-dependent reversible route with the normal-quotient structure exposed
  bcs-projective-kernel-phase-compilation: that seeks a distinguished finite-gadget phase word in a tracial projective kernel; this permits any centralizable one-player word system and formulates soundness directly as separation of state faces
  perfect-lcs-gap-implies-nonhyperlinear: an LCS instance would satisfy this through its solution-group relations; this does not require the compiler output to have LCS syntax
---

**OPEN.**  Start with the fixed finite synchronous BCS whose algebra has a
tracial state but no `R^U` state.  Construct one finite torically determined
two-player game with phase group `B`, player groups `G_A,G_B`, and clause
words

```text
beta_i a_i b_i,
a_i in G_A,
b_i in G_B,
```

such that all three properties hold:

1. the full target universal group algebra has a tracial state fixing every
   clause and representing `B` by its faithful scalar character;
2. the entire target clause-character face is disjoint from the weak-star
   closure of finite-dimensional vector states, quantitatively by decoding a
   near-perfect finite target strategy to a forbidden near-perfect finite BCS
   strategy; and
3. the source nonlinear predicates are encoded after the forced
   centralizations of all `a_i,b_i`, rather than only on one selected finite
   packet type.

Property 1 certifies phase-safe normal closure.  Property 2 is exactly the
relative-FD criterion in `toric-gap-is-a-relative-fd-central-word-face`.
Property 3 is load-bearing: the exact normal quotient is a central quotient
of the two one-player centralization quotients, so a noncentral reversible
circuit that works only in an intended packet representation does not prove
the target theorem.

Local finite controlled-reflection gadgets remain possible, but finite-group
induction recreates forbidden selector types.  The missing actuator must
therefore be global/state-dependent or genuinely finite-dimensional-only.
The categorical finite-Morita obstruction, including matrix amplification
and full corners, is proved in
`finite-morita-toricization-cannot-encode-nonaffine-support`.

Two finite-packet shortcuts are now excluded before quantitative soundness.
`spherical-root-type-selection-is-phase-unsafe` shows that a transitive
`H/K` root can isolate the desired answer type on the cyclic vector, but its
moving inducing character kills the scalar phase under normal closure.
`extraspecial-spin-predicate-centralization-kills-phase` shows that a
noncentral Pauli predicate word, even behind a private conjugator, has a
commutator equal to the common phase and is therefore killed when the toric
clause centralizes that word.  Thus Properties 1 and 3 cannot be obtained by
simply anchoring one finite selected type or one conjugated spin word.
Moreover `product-word-stabilizers-cannot-linearize-one-losing-corner` rules
out an all-allowed-states local dilation: product words fixing the three
allowed Boolean rectangles automatically fix the fourth.  The only surviving
finite-ancilla interpretation is genuinely state-dependent and must prove the
whole-face soundness in Property 2.

## Property 2: the minimal quantitative decoder

Property 2 has a precise sufficient interface which does not depend on the
choice of gadget in Properties 1 and 3.  Let `R_B` be the fixed finite list of
involution, within-context commutator, and forbidden-product polynomials in
`non-ce-bcs-has-robust-approximate-energy-gap`, and let `beta_B^rob>0` be its
gap.  For unitaries `Z_x in M_d(C)` and a density matrix `rho` define

```text
E_B(rho,Z)=sum_(R in R_B) Tr(rho R(Z)^*R(Z)).           (CWF1)
```

> **Weighted tracial decoder lemma.**  If `rho>=0`, `Tr(rho)=1`, and
> `[rho,Z_x]=0` for every BCS variable, then
>
> ```text
> E_B(rho,Z)>=beta_B^rob.                               (CWF2)
> ```

Indeed, write the spectral decomposition
`rho=sum_j lambda_j Q_j`.  Every `Q_j` reduces every `Z_x`.  Applying the
normalized-HS robust gap on the nonzero corner `Q_j C^d` gives

```text
sum_(R in R_B) tau_(Q_j)(R(Z)^*R(Z))>=beta_B^rob.
```

Multiplication by `lambda_j rank(Q_j)` and summation proves `(CWF2)`, because
those coefficients are nonnegative and sum to `Tr(rho)=1`.

Consequently it is enough for a target compiler to map every
finite-dimensional target vector state `(pi,xi)` to `(rho,Z)` as above and
prove, for one constant `C` independent of dimension,

```text
E_B(rho,Z)<=C E_target(pi,xi).                          (CWF3)
```

Then `(CWF2)--(CWF3)` give
`E_target(pi,xi)>=beta_B^rob/C`.  This excludes not just one intended target
state but the entire weak-star finite-dimensional clause face: a sequence of
finite-dimensional vector states converging to that face would have target
energy tending to zero, contradicting the same bound.

The commutant condition in this lemma is load-bearing.  The target face is
made of arbitrary finite-dimensional **vector** states, whose natural density
is rank one.  There is no dimension-free comparison between
`Tr(rho X^*X)` and the normalized Hilbert--Schmidt norm of `X`; for example a
rank-one `rho` gives zero weight to every operator supported on its orthogonal
complement.  Centralization of the target clause words does not by itself put
the decoded BCS variables in `rho'`.  Thus
`non-ce-bcs-has-robust-approximate-energy-gap` alone cannot prove Property 2
from abstract centralizable words: the missing construction must either
produce the commuting density in `(CWF1)--(CWF3)`, or retain the vector-state
weight and use the already recorded Gram decoder
`one-gram-vector-decodes-a-finite-bcs-strategy` together with the static
finite-game gap.  Merely bounding normalized-HS BCS energy is not a
whole-face decoder.
