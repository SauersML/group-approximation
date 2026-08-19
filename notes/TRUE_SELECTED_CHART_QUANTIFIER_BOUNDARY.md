# Selected `SL_3(Z)` carry bounds do not yet cross the universal TRUE gate

Date: 2026-08-11

## Purpose

The projective `SL_3(Z)` calculations have produced exact mathematics: a
universal real Hodge gap, an exact discriminant formula for the circle
carry constant, the first three integral stabilizer homology groups, and a
harmonic dual-systole criterion.  This note fixes their logical scope in the
proof that every hyperlinear group is sofic.

There are two separate issues.

1. The selected projective charts concern one fixed base group and one
   chosen residual-finite action family.  The common-Cartan reduction for a
   general hyperlinear group produces an arbitrary sofic quotient action,
   with additional relatively-Haar colors prescribed by the original
   monomial model.
2. Although every individual finite chart has a finite carry constant,
   its phase defect is produced simultaneously with the chart.  Ordinary
   repetition or dilution cannot request a smaller defect while retaining
   that same chart.

Both points are exact.  In particular, even a proof of a uniform projective
`SL_3(Z)` carry bound would be a strong selected-family theorem, not by
itself a proof of the full hyperlinear-to-sofic implication.

## The actual dependency chain

For a countable hyperlinear group `Gamma`, the current TRUE route is:

`hyperlinear matrix tables`
` -> common approximately invariant Cartans`                    `(SCQ1)`

` -> 1 -> K -> Gamma -> Q -> 1`,
`    K abelian, Q sofic, with a Haar phase cocycle`              `(SCQ2)`

` -> finite models of the prescribed colored Q-action`
`    whose phase defect is close to the exact cocycle locus`     `(SCQ3)`

` -> exact finite-phase tables -> a sofic approximation`.       `(SCQ4)`

The implications after the hypotheses in `(SCQ1)` and `(SCQ3)` are proved
in `TRUE_CARTAN_MONOMIAL_GATE.md`, `TRUE_HAAR_PHASE_KERNEL.md`, and
`POPA_FACTOR_MODEL_LIFTING.md`.  What is not proved is:

* existence of the common Cartans in `(SCQ1)` for arbitrary hyperlinear
  tables; and
* the phase completion `(SCQ3)` for the arbitrary prescribed sofic action
  arising in `(SCQ2)`.

By contrast, the projective carry complex has

`Q=SL_3(Z)`, `V_p=P^2(F_p)`.                           `(SCQ5)`

A bound for its constants proves circle repair for phase tables on the
specific complexes `(SCQ5)`.  It neither constructs the Cartans in
`(SCQ1)` nor replaces the arbitrary quotient `Q` and its colored action in
`(SCQ2)--(SCQ3)` by `(SCQ5)`.  No such replacement theorem occurs in the
current notes.  Thus the projective family is a rigorous testbed for the
integral nonlinear mechanism, and could close a special `SL_3(Z)`-based
phase instance, but it is not presently the universal bridge.

## Carry constants under disjoint amplification

Let `A_i:E_i->F_i` be finite integral linear maps.  Equip the direct sums
with their orthogonal Euclidean norms, put

`W_i=ran_R(A_i)`, `L_i=W_i intersect (F_i)_Z`,          `(SCQ6)`

and define

`Theta(A_i)=sup_(z in (F_i)_Z minus L_i)`
`  dist(z,L_i)/dist(z,W_i)`.                           `(SCQ7)`

For the direct sum `A=directSum_i A_i`, one has

`W=directSum_i W_i`, `L=directSum_i L_i`.              `(SCQ8)`

**Proposition 1 (direct-sum rigidity).**

`Theta(directSum_i A_i)=max_i Theta(A_i)`.             `(SCQ9)`

In particular,

`Theta(A^(directSum r))=Theta(A)`                      `(SCQ10)`

for every positive integer `r`.

**Proof.**  Write `z=(z_i)`.  Orthogonality and `(SCQ8)` give

`dist(z,L)^2=sum_i dist(z_i,L_i)^2`,
`dist(z,W)^2=sum_i dist(z_i,W_i)^2`.                  `(SCQ11)`

If `C=max_i Theta(A_i)`, applying the defining inequality in every
coordinate gives

`dist(z,L)^2<=C^2 dist(z,W)^2`.                       `(SCQ12)`

Hence the left side of `(SCQ9)` is at most `C`.  Conversely, place an
arbitrary carry from one component in that component and put zero in all
others.  Its ratio is unchanged, so the supremum is at least every
`Theta(A_i)`.  This proves `(SCQ9)--(SCQ10)`.  End proof.

The same conclusion holds with normalized Euclidean norms: both distances
are multiplied by the same normalization factor.

## Repetition and dilution do not improve the defect/repair ratio

For a circle phase vector `x`, write

`def_A(x)=dist(Ax,F_Z)`,
`rep_A(x)=dist(x,{y:Ay in F_Z})`.                     `(SCQ13)`

Use normalized squared norms on a disjoint union of `r` equal charts.  If
`x^(r)=(x,...,x)`, then

`def_(A^(directSum r))(x^(r))=def_A(x)`,
`rep_(A^(directSum r))(x^(r))=rep_A(x)`.              `(SCQ14)`

Indeed the nearest integer carry and nearest repaired phase may be chosen
componentwise, and the sum of `r` identical squared distances is divided by
`r`.

More generally, put the phase table on only an `alpha` fraction of the
components and put an exact table on the rest.  Then

`def_new=sqrt(alpha) def_A(x)`,
`rep_new=sqrt(alpha) rep_A(x)`.                       `(SCQ15)`

Thus the ratio is unchanged.  In a monomial trace model, the trace signal
of the active block is diluted at least as fast, so this operation does not
create a better separation budget either.

**Corollary 2 (quantifier obstruction).**  Let `(A_n,x_n)` be phase tables
produced jointly by a model construction, with

`delta_n=def_(A_n)(x_n) -> 0`, `C_n=Theta(A_n)`.       `(SCQ16)`

The integral factorization theorem gives qualitative repair from the
available data when

`C_n delta_n -> 0`.                                  `(SCQ17)`

Finiteness of every individual `C_n` does not imply `(SCQ17)`.  Disjoint
repetition and exact-block dilution cannot turn `(SCQ16)` into `(SCQ17)`.

**Proof.**  The repair estimate is

`rep_(A_n)(x_n)<=constant * (1+C_n) delta_n`;          `(SCQ18)`

see `TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md`.  The first assertion follows.
Proposition 1 and `(SCQ14)--(SCQ15)` prove the second.  End proof.

This does not rule out a genuinely new resampling operation which holds the
base chart and its colored statistics fixed while improving the phase
defect.  Such an operation would itself prove a strong form of the missing
model-selection/cocycle-stability theorem `(SCQ3)`; it is not supplied by
standard amplification.

## Correct research target

There are now two legitimate uses of the projective computation.

1. Determine the truth of uniform integral circle stability on the
   `SL_3(Z)` projective family.  This can reveal a real arithmetic mechanism
   or a concrete carry instability, and it directly controls selected
   models based on `(SCQ5)`.
2. Extract from any successful proof a **group-independent** selection
   principle applying to the prescribed colored sofic action in `(SCQ3)`.

Without the second step, farming more projective primes cannot prove the
main theorem.  The universal target remains the normal free-group character
transfer in `AGENDA.md`: a positive fixed-point loss certificate for finite
actions must be incompatible with a normal `0/1` character that is a limit
of finite-dimensional unitary characters.  Equivalently, one must prove
the common-Cartan and arbitrary-action completion gates, or bypass them by
a direct finite-action character construction.
