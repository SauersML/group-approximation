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

## Properties 1 and 3: the exact algebraic boundary

The established predicate-phase word does give Property 1 on a selected
tracial BCS state, and it does so without endangering the scalar phase.  The
failure is precisely Property 3.

Fix one context `c`, with variables `U_c`, allowed support
`R_c subset {+1,-1}^(U_c)`, and let

```text
f_c(a)=1_(R_c)(a) in F_2.                              (CWA1)
```

Apply `boolean-predicate-central-phase-word` to `f_c` and to every coordinate
function `a |-> a_x`.  Taking the finite direct product of those gadgets gives
a finite group `K_c`, central involutions

```text
w_c, z_(c,x) in Z(K_c),                                (CWA2)
```

and, for every assignment `a`, a finite-dimensional representation
`pi_(c,a)` such that

```text
pi_(c,a)(w_c)=(-1)^(f_c(a)) I,
pi_(c,a)(z_(c,x))=a_x I.                               (CWA3)
```

There are only finitely many assignments, so amplify the `pi_(c,a)` to one
common dimension.  Let `(M,tau)` be a perfect tracial BCS model, let `Z_x`
be its context involutions, and put

```text
P_(c,a)=product_(x in U_c) (1+a_x Z_x)/2.              (CWA4)
```

The `P_(c,a)` form a PVM, and perfection gives `P_(c,a)=0` for
`a notin R_c`.  Hence

```text
rho_c(k)=sum_a P_(c,a) tensor pi_(c,a)(k)              (CWA5)
```

is a representation of `K_c` in a finite amplification of `M`, with

```text
rho_c(z_(c,x))=Z_x tensor I,
rho_c(w_c)=-I.                                         (CWA6)
```

Use separate finite ancilla factors for the finitely many contexts.  Their
representations combine to a representation of the free product of the
`K_c`; repeated variables agree by the first identity in `(CWA6)`.  Adjoin a
central involution `J`, represent it by `-I`, and impose the central predicate
clauses

```text
J w_c=1.                                               (CWA7)
```

The amplified trace fixes every clause and is faithful on `<J>`.  It
therefore certifies that the normal closure of these clauses does not kill
`J`.  This is a completely phase-safe, state-conditioned realization of the
local nonlinear predicates.  In particular, phase survival itself is not the
missing algebraic step.

It does **not** encode the predicate on the whole central-word face.  Put

```text
D_c=<z_(c,x):x in U_c> <= Z(K_c).                      (CWA8)
```

The representations in `(CWA3)` realize every character of `D_c`.  If
`f_c` is nonlinear, then `w_c notin D_c`: otherwise evaluation of the group
element `w_c` on those characters would be an affine character of the
selector bits, contrary to `(CWA3)`.  Therefore, for
`C_c=<D_c,w_c>`, every selector character has two extensions to `C_c`, one
with each value of `w_c`.  Inducing either extension from `C_c` to `K_c`
and taking an irreducible constituent preserves all these central scalar
values.  In particular, for every forbidden assignment `a notin R_c` there
is an exact finite-dimensional sector with

```text
z_(c,x)=a_x I for every x,          w_c=-I.             (CWA9)
```

Setting `J=-I` makes `(CWA7)` exact on this forbidden sector.  Thus forced
centralization retains, rather than removes, a phase-compatible forbidden
type.  This is the selector-induction mechanism of
`controlled-central-phase-finite-group-barrier`, now applied directly to the
state-conditioned construction `(CWA5)`.

Solution groups mark the sharp boundary.  For affine predicates the phase
word belongs to the selector subgroup, so ordinary solution-group relations
can impose it; `solution-group-central-order-is-operator-solvability` then
turns full order of `J` into a phase-faithful operator model, and
`slofstra-zhang-high-girth-phase-survival` can certify that order.  For a
nonlinear predicate, `(CWA9)` shows that replacing the predicate by a finite
central word has not produced a solution-group relation at all.  High girth
can protect an already compiled linear phase, but it cannot remove these
local forbidden central characters.

Consequently the finite predicate-phase word settles the selected-trace half
of Property 1 but cannot settle Property 3.  Any positive compiler must add a
genuinely global coupling which excludes the sectors `(CWA9)` only after
contexts are assembled, while preserving the trace `(CWA5)`.  Merely adding
finite table relations, centralizing the predicate word, or importing a
solution-group phase-survival certificate cannot do so.

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
