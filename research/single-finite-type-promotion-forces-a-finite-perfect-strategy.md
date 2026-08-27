---
rg: 2
id: single-finite-type-promotion-forces-a-finite-perfect-strategy
kind: claim
title: Promoting every context through one covariant finite type forces a finite perfect strategy
distinct_from:
  role-hyperoctahedral-type-has-an-orthogonal-amalgam-model: that shows separate selected context types can rotate to orthogonal subspaces inside one common D8 multiplicity reservoir; this shows that rigidly identifying them through one finite type destroys exact infinite-only completeness.
  shared-multiplicity-commutator-builds-selected-hybrid-row: that constructs one predicate row on one selected type and cancels its arbitrary multiplicity commutator in the outer D8 test; this proves that placing all such rows on one covariantly transported type would make the finite factor itself a perfect strategy.
  common-source-partial-isometries-decode-one-game-state: that proves a quantitative finite-matrix game-gap inequality from arbitrary common-source partial isometries; this isolates the finite-type tensor factorization which makes the same conclusion hold even in an infinite exact representation.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that rules out a universally scalar nonlinear row on the whole marked regular sector; this permits selected non-scalar rows but rules out promoting all of them by one type-preserving finite packet.
---

Let `B` be a finite constraint-variable BCS game with

```text
omega^*(B)<=theta<1.                                      (SFT1)
```

A tempting way to finish the D8 common-source compiler is to put every
context truth-table packet on one selected finite type and make every
context transport preserve that type.  This does eliminate the
orthogonal-carrier rotation.  It also eliminates the finite/infinite
asymmetry needed for exact completeness.

## Finite-type promotion datum

Let `V` and `W_c` be nonzero finite-dimensional Hilbert spaces.  On `W_c`
let

```text
(p_(c,a))_(a in A_c)                                    (SFT2)
```

be a PVM, with forbidden projection `f_c` and context involutions

```text
a_(c,x)=sum_a a_x p_(c,a).                              (SFT3)
```

Let `M` and `N_c` be arbitrary nonzero Hilbert spaces, finite or infinite.
The source and context carriers are

```text
V tensor M,                    W_c tensor N_c.           (SFT4)
```

Assume the context transport is covariant for the selected finite types.
Schur factorization then has the form

```text
S_c=s_c tensor U_c,                                      (SFT5)
```

where `s_c:V->W_c` and `U_c:M->N_c` are isometries onto the
corresponding carrier ranges.  The selected context PVM is

```text
P_(c,a)=p_(c,a) tensor I_(N_c).                          (SFT6)
```

Finally let `B_x` be one common source involution on `V tensor M` for each
global variable, and suppose the exact predicate and consistency rows hold:

```text
(f_c tensor I) S_c=0,
(a_(c,x) tensor I) S_c=S_c B_x.                         (SFT7)
```

This is exactly the tensor form produced when a finite packet type is
selected and every HNN/covariance implementer preserves that type.  An
arbitrary multiplicity unitary is allowed in `U_c`; no scalar orientation
or finite multiplicity is assumed.

## Theorem: the multiplicity space cancels

Every datum `(SFT2)--(SFT7)` produces a finite-dimensional perfect strategy
for `B` on `V`.  Consequently no such nonzero datum exists under `(SFT1)`,
even when all multiplicity spaces in `(SFT4)` are infinite-dimensional.

### Proof

Pull the context atoms back along the finite part of the transport:

```text
tilde p_(c,a)=s_c^* p_(c,a) s_c in End(V).              (SFT8)
```

Because the target atoms reduce the range of `s_c`, these form a PVM on
`V`.  The tensor pullback is

```text
S_c^* P_(c,a) S_c
 =tilde p_(c,a) tensor I_M.                             (SFT9)
```

The first row of `(SFT7)`, followed by multiplication by `S_c^*`, gives

```text
s_c^* f_c s_c=0.                                       (SFT10)
```

Thus the finite PVM `(SFT8)` assigns zero weight to every forbidden answer.
The second row gives

```text
B_x=S_c^*(a_(c,x) tensor I)S_c
   =(s_c^*a_(c,x)s_c) tensor I_M.                      (SFT11)
```

The left side is independent of `c`.  Hence, whenever `x` belongs to both
`c` and `d`, the finite matrices

```text
beta_x=s_c^*a_(c,x)s_c=s_d^*a_(d,x)s_d                 (SFT12)
```

agree.  Use the PVMs `(SFT8)` for the context player and the binary PVMs of
the finite involutions `beta_x` for the variable player, with a maximally
entangled state on `V tensor conjugate(V)`.  Equations `(SFT10)--(SFT12)`
make every predicate and incidence test perfect.  This is a
finite-dimensional perfect strategy, contradicting `(SFT1)`.  Notice that
the operators `U_c` disappeared already in `(SFT9)`; infinite multiplicity
cannot repair the contradiction.  QED.

The same argument allows a common nonzero multiplicity projection
`Q in B(M)`: restrict to `V tensor Q M` first.  It also allows rectangular
target spaces and partial isometries, provided the initial projection is
the full selected source and the context atoms reduce the target range.

## Stronger monomial consequence

For the tautological hyperoctahedral type, the obstruction is classical.
Suppose `V=C^Omega`, every `p_(c,a)` is a coordinate projection, and every
finite transport `s_c` is a signed permutation between coordinate bases.
Then all pulled-back PVMs `(SFT8)` lie in the same diagonal MASA of
`End(C^Omega)`.  For each `omega in Omega`, let `a_c(omega)` be the unique
context answer selected by `tilde p_(c,a)` at that coordinate.  Equation
`(SFT12)` says

```text
a_c(omega)_x=a_d(omega)_x                              (SFT13)
```

whenever the contexts share `x`, while `(SFT10)` says every `a_c(omega)`
is allowed.  Thus every coordinate `omega` gives a single global Boolean
assignment satisfying every constraint.

Therefore identifying all role-hyperoctahedral context types by literal
signed-permutation transports does not merely create a finite quantum
strategy.  It forces a classical perfect solution.

## Direct audit of the one-global-role-packet candidate

Here is the most economical proposed construction.  Let `C` be the finite
context set and take one coordinate packet

```text
Omega=({src} union C) times Lambda times {0,1}_duplicate, (SFT14)
H=(C_2)^Omega semidirect Sym(Omega).
```

The set `Lambda` stores all local assignment labels (or all gauge-share
labels).  On the tautological type `T=C^Omega`, let `j_c` be a signed
permutation swapping the source role with role `c`.  Put the context
predicate sign only on role `c`, use the doubled signed-permutation
commutator to wordize it, and use the source role for every global variable.
All contexts now have the same primitive central idempotent `q_T`; their
selected sources cannot rotate to orthogonal isotypic carriers.

There is already a small D8 syntax defect in the literal version.  In the
tautological signed-permutation representation, the only scalar sign used
as the common central mark is `y=-I`.  If `z` is diagonal and `j` is a
signed permutation involution, then

```text
[z,j]=y
```

holds exactly iff the diagonal signs of `z` are opposite at the two ends of
every `j`-orbit.  In particular `j` has no fixed coordinate.  A permutation
which swaps only `src` with `c` and fixes all other role coordinates is
therefore not a D8 swap with central mark `-I`.  One may repair this by also
pairing all unused roles, or by using separate supported central signs in a
smaller role-preserving subgroup.  Neither repair affects the semantic
obstruction below, so grant the candidate this repair.

This candidate has an exact and fatal pointwise consequence.  For
`lambda in Lambda`, write

```text
a_(c,x)(lambda) in {+1,-1}
```

for the context-`c` answer read at the coordinate reached from
`(src,lambda)` by `j_c`, and write `b_x(lambda)` for the source-role value of
the literal global variable.  Exact consistency of the D8 row gives

```text
a_(c,x)(lambda)=b_x(lambda)                            (SFT15)
```

for every incidence `(c,x)` and every source coordinate.  Exact predicate
rows give

```text
(a_(c,x)(lambda))_(x in c) in R_c.                    (SFT16)
```

Therefore, for every source coordinate `lambda`, the values

```text
x |-> b_x(lambda)                                     (SFT17)
```

form a global Boolean assignment whose restriction to every context is
allowed.  The candidate has an exact marked model only if the BCS has a
classical perfect solution.

The conclusion is unchanged if each `j_c` applies a context-dependent
permutation to `Lambda`: use the pulled-back label `j_c(src,lambda)` in
`(SFT15)`.  It is also unchanged if the context role spaces are disjoint or
have different coordinate repetitions.  The common source coordinate
still chooses one answer for every global variable, and every transported
context reads that same answer on its incidences.

### Multiplicity factors do not repair the candidate

On the `T`-isotypic component, complete finite covariance forces

```text
j_c=J_c tensor U_c,
d_(c,x)=D_(c,x) tensor V_(c,x),                        (SFT18)
```

with the multiplicity factors independent of the coordinate `lambda`.
The shared-commutator predicate construction deliberately arranges the
same multiplicity word on both roles, so the outer D8 commutator cancels it.
For a consistency row, the same calculation leaves precisely the finite
coordinate mismatch

```text
a_(c,x)(lambda) b_x(lambda).                          (SFT19)
```

A coordinate-independent multiplicity unitary cannot change `(SFT19)` on
only the mismatching coordinates.  If different role factors are allowed,
their ratio would have to be simultaneously `+I` on matching coordinates
and `-I` on mismatching coordinates, contrary to Schur factorization unless
one of those sets is empty.  The exceptional all-mismatching case is exactly
the global relative-role sign twist.  It is excluded by the literal
oriented consistency word (or by
`centralizing-d8-word-anchors-relative-row-orientation`); if it is retained,
the packet is not compiling the original BCS consistency test.  Thus a
correctly oriented exact row again gives `(SFT15)`.

### Gauge shares do not repair the candidate

Replace each logical bit by two shares and let the gauge group flip both
shares.  At a source coordinate define the logical value to be their
product.  Exact consistency says that the products, not the individual
shares, agree between every incident context and the source.  Exact
predicate rows evaluate `f_c` on those same products.  Hence `(SFT17)` is
again a global satisfying assignment.  Gauge orbits can hide which share
carries a sign; they cannot make one logical product take incompatible
values at the same source coordinate.

Consequently the one-global-role-packet candidate is ruled out for the
static source game in `(SFT1)`.  It defeats carrier rotation only by making
the exact witness classical coordinate by coordinate.

## Corollary: a unique marked finite type is not the repair

One might enlarge the packet so that its central marked sector contains a
single irreducible type, as happens for the spin sector of an extraspecial
group.  If every context row and transport preserves that type, an exact
marked representation has the form `(SFT4)--(SFT7)` by Schur's lemma.
The theorem then extracts the same finite perfect strategy from the finite
factor.  Hence making the selected type exhaust the common D8 mark would
solve soundness only by killing the required perfect infinite witness.

This is the exact promotion dilemma:

```text
separate finite context types
  -> their selected carriers rotate independently (orthogonal-amalgam escape);

one covariantly preserved finite type
  -> the multiplicity cancels and a finite perfect strategy appears.       (SFT20)
```

The remaining compiler cannot be a static finite-type identification.  It
must use a feature absent from `(SFT5)`, for example type-changing Hecke
transport, a properly infinite return, or a finite-matrix-only joint energy
inequality which charges relative carrier rotation without imposing exact
type preservation in the infinite witness.

## Application to the shared-commutator hybrid row

On one selected context type,
`shared-multiplicity-commutator-builds-selected-hybrid-row` gives

```text
e_c=D_c tensor V_c,                                    (SFT21)
```

and the outer D8 commutator cancels `V_c`.  If all context selected types
are promoted to one common covariant carrier, the context truth-table PVMs
and the D8 transports satisfy `(SFT6)--(SFT7)`.  The cancellation which is
so useful locally is exactly what makes the infinite multiplicity invisible
in `(SFT9)--(SFT11)`.  Therefore `(SFT21)` closes the local predicate row
but cannot be promoted by a single finite multi-role type.

## Attempts and firewalls

- **Use countably infinite amplification.**  Equations `(SFT9)--(SFT12)`
  remove the amplification factor before any dimension count.
- **Allow one arbitrary multiplicity unitary per context.**  Every `U_c`
  cancels between `S_c^*` and `S_c`.
- **Use one unique central marked irreducible.**  This enforces the tensor
  form more strongly and triggers the corollary.
- **Put every hyperoctahedral context into one larger coordinate packet.**
  Signed-permutation transport puts all pullbacks in one MASA and forces a
  classical global solution.
- **Conclude that selected-type compilers are impossible.**  Too strong.
  Separate selected types plus a non-universal matrix-only actuator could
  charge their relative rotation without satisfying `(SFT5)` exactly.
- **Conclude non-hyperlinearity.**  This is a no-go for one promotion
  architecture, not the missing actuator.
