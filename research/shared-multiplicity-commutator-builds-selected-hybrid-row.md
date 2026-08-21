---
rg: 2
id: shared-multiplicity-commutator-builds-selected-hybrid-row
kind: claim
title: A shared multiplicity commutator builds the hybrid predicate row on one selected type
distinct_from:
  finite-role-packet-cannot-supply-hybrid-predicate-row: that rules out a universally scalar ordinary-word row on the whole marked finite regular sector; this deliberately leaves one arbitrary multiplicity commutator in the row and cancels it only in the final D8 swap test.
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that computes an AND from controlled Pauli gates and identifies the residual multiplicity commutator; this shows the residual is harmless when it is common to the two D8 roles and gives an arbitrary-predicate signed-permutation construction.
  dihedral-spin-packet-supplies-common-partial-swap: that supplies the common partial swap and reduces soundness to hybrid row commutators; this constructs such a row on a fixed selected finite type but does not promote that type to the common source across different contexts.
  selector-correlated-direct-power-router: that cancels the multiplicity unitary inside a balanced router word; this keeps the multiplicity commutator and uses the outer common-swap commutator to erase it.
  centralizing-d8-word-anchors-relative-row-orientation: that fixes the remaining relative role twist by one tautological D8 anchor while allowing arbitrary whole-row multiplicity; this constructs the nonlinear selected row whose harmless common factor is compatible with that anchor.
---

The free external multiplicity factor in a role-covariant reversible circuit
does not have to be killed.  It is enough that the **same** factor occur on
both D8 roles.  The final commutator with the common role swap cancels it
exactly.

## Sign-safe shared-factor identity

Let `K` be a finite-dimensional logical label space, let `M` be an arbitrary
multiplicity space, and work on

```text
H=(C^2_role tensor K) tensor M.                         (SMC1)
```

Let

```text
j=X_role tensor I_K tensor I_M                         (SMC2)
```

be the common D8 swap.  For an arbitrary unitary `V on M` and an arbitrary
unitary `h on K`, put

```text
e=(|0><0| tensor h+|1><1| tensor I_K) tensor V.         (SMC3)
```

Then

```text
[e,j]
 =diag(h,h^(-1)) tensor I_M,                            (SMC4)
```

up to the harmless choice of multiplicative commutator convention.  In
particular, if `h=h^*=h^(-1)`,

```text
||[e,j]-I||_2^2
 =||h-I||_(2,K)^2.                                     (SMC5)
```

Both norms in `(SMC5)` are normalized on their displayed full spaces.  The
two role blocks of `[e,j]-I` are `h-I` and `h^(-1)-I`, each repeated
`dim(M)` times.  Division by `2 dim(K) dim(M)` gives the average of their two
normalized squared norms; for an involution `h` they are equal.

The arbitrary `V` disappears exactly.  The same statement holds on a
partial D8 source: if the swap block is `S=S_0 tensor I_M`, then the
off-diagonal additive commutator is

```text
(h-I)S_0 tensor V,                                     (SMC6)
```

so its normalized-HS energy is again independent of `V`.

This is the important correction to the tempting stronger target.  One does
not need an ordinary word equal to `diag(h,I)`.  A word equal to
`diag(h,I) tensor V` for one common, completely uncontrolled `V` gives the
same D8 test.

## Every doubled truth table is one finite signed-permutation commutator

Let `Omega_0` be the finite label set consisting of one role bit and the
Boolean assignment labels required by one fixed context.  For a predicate
`f`, let `D_f` be the diagonal sign

```text
D_f(r,x)=(-1)^(f(x))  if r=0,
D_f(r,x)=+1          if r=1.                           (SMC7)
```

Duplicate every label by one inert bit and put

```text
Omega=Omega_0 times {0,1},
D=D_f tensor I_2.                                      (SMC8)
```

The number of negative entries of `D` is even.  Choose one cyclic
permutation `P` of `Omega`.  If its cyclic order is `omega_0,...,omega_(n-1)`
and `d_i` is the sign of `D` at `omega_i`, choose signs recursively by

```text
s_0=1,                 s_i=d_i s_(i-1).                (SMC9)
```

Even parity of the negative set is exactly the consistency condition around
the cycle.  For the diagonal sign `S=diag(s_i)`, direct calculation gives

```text
[S,P]=D                                                    (SMC10)
```

after choosing the matching inverse convention.  Both `S` and `P` lie in
the finite hyperoctahedral group

```text
B_Omega=(C_2)^Omega semidirect Sym(Omega),              (SMC11)
```

and its tautological signed-permutation representation is irreducible.
Thus arbitrary Boolean nonlinearity has been reduced to one commutator of
two fixed finite packet constants.  The inert duplication changes no
normalized rejection density.

## Role-covariant stable implementers share one external factor

Let `rho` be the tautological irreducible representation of `B_Omega`.
Adjoin two implementers `u,v` with the complete finite covariance tables

```text
u k u^(-1)=S k S^(-1),
v k v^(-1)=P k P^(-1)              for every k in B_Omega. (SMC12)
```

On every `rho`-isotypic carrier, Schur factorization gives

```text
u=S tensor R,                    v=P tensor T             (SMC13)
```

for arbitrary multiplicity unitaries `R,T`.  Therefore the ordinary word

```text
e=[u,v]                                               (SMC14)
```

has the exact form

```text
e=D tensor [R,T].                                     (SMC15)
```

Regard the duplicate bit as part of `K` and let the role swap `j` be the
signed-permutation packet element which exchanges the two role labels while
fixing the assignment and duplicate labels.  Equations `(SMC4)--(SMC5)` now
give

```text
[e,j]=diag((-1)^f,(-1)^f) tensor I_duplicate tensor I_M,
||[e,j]-I||_2^2
 =4 Pr_x[f(x)=1].                                     (SMC16)
```

Thus `[e,j]` is the **rejection phase**, not the identity as an algebraic
identity.  The presentation names the relator

```text
[e,j]=1.                                              (SMC16a)
```

It is exact on allowed labels `f(x)=0`; every rejecting label contributes
squared unitary distance `|-1-1|^2=4`.  The duplicate bit has identical
phase on both values and therefore cancels from the normalized fraction.

The external multiplicity commutator `[R,T]` is completely arbitrary and
need not be oriented, scalar, or close to the identity.

The covariance extensions in `(SMC12)` are not mysterious HNN dynamics.
Because both automorphisms are inner, `S^(-1)u` and `P^(-1)v` centralize the
finite base.  This is exactly why the same external factors appear in both
roles and exactly why the D8 test can cancel them.

## Robust fixed-packet form

For the complete table of the fixed finite group `B_Omega` and the two fixed
covariance menus `(SMC12)`, finite-group HS exactification plus polar
alignment yields the same conclusion with `O(sqrt(E))` error, where `E` is
the sum of the named packet/covariance defects.  All constants depend only
on the fixed context truth table and not on ambient matrix dimension or on
the multiplicities of `rho`.

No estimate on `[R,T]` is used.  After exactification the outer commutator
with `j` removes it algebraically; before exactification, a fixed word
telescoping estimate adds only the fixed packet modulus.

## Exact-completeness firewall

Use the finite support menu from
`private-gauges-close-fanizza-triangle`.  For one arity-`k` context, index
the menu by every nonempty support

```text
T subset {+1,-1}^k,                                  (SMC16b)
```

and on its factor use

```text
L divisible by |T| for every nonempty T,
Omega_T={0,1}_role times T times [L/|T|]
        times {0,1}_duplicate.                        (SMC16c)
```

Perform `(SMC8)--(SMC15)` with `f` restricted to `T`.  A menu type `rho_T`
uses the tautological representation on the `T` factor and the trivial
representation on the other factors.  Every tautological type now has the
same dimension `4L`, and every assignment in `T` has the same multiplicity.
The final duplicate still makes the number of negative coordinates even.

If an exact perfect context model has nonzero joint support `T_0`, then

```text
T_0 subset f^(-1)(0).                                 (SMC16d)
```

After countable amplification, the context tuple is unitarily equivalent to
the selector tuple in `rho_(T_0)`.  On this type `D=I`, so take `S=I` in
`(SMC9)` and choose the external factors trivially.  Then `e=I` and the
relator `(SMC16a)` holds exactly.  Every unused menu factor is represented
trivially.  The existing gauge-orbit and incidence-private half-edge
construction extends all finitely many contexts simultaneously and leaves
the native marked word on its original factor.

This is the precise firewall:

```text
perfect allowed support -> exact extension of every hybrid-row relator.
                                                               (SMC16e)
```

It does not assert that `(SMC16a)` holds on a packet type containing a
rejecting label.  There the final word is intentionally `-1` on that label
and supplies soundness energy.

## What this closes and what it does not

For one selected hyperoctahedral type, the hybrid-row construction is now
complete:

```text
arbitrary predicate f
 -> doubled diagonal sign D
 -> one signed-permutation commutator [S,P]
 -> role-covariant word [u,v]
 -> D8 test [ [u,v], j ] with no multiplicity residue. (SMC17)
```

This construction evades
`finite-role-packet-cannot-supply-hybrid-predicate-row` because `(SMC15)` is
not a universally scalar hybrid reflection.  It carries the arbitrary
operator `[R,T]`, and only the tested commutator `(SMC16)` is scalar.

It does **not** prove that the selected tautological carrier occupies the
same positive-density D8 source for every BCS context.  Separate context
packets may select disjoint isotypic carriers, while putting all contexts in
one finite tensor packet would impose illegal cross-context commutation.
The result therefore closes the local role-orientation and external-factor
problems, and leaves the already separate selected-carrier/common-source
promotion problem untouched.

The sole remaining promotion/alignment axiom can be stated without any
orientation language.  Let `Q_(c,T)` be the selected tautological-type
projection for context `c` and support-menu factor `T`, after fixed packet
exactification, and let `S_D8` be the single partial isometry extracted from
the common D8 swap.  It is enough to prove a dimension-independent
`kappa>0` and `omega(delta)->0` such that

```text
sum_(c,T) ||([e_(c,T),j]-1) Q_(c,T)||_2^2
 >= kappa E_BCS(S_D8)-omega(delta),                    (SMC18)
```

where `E_BCS(S_D8)` is the finite-game Gram-row energy formed from that
**same** partial source and the shared literal variable words.  The
`Q_(c,T)` must be coupled jointly: separate contextwise Plancherel lower
bounds are insufficient because the selected carriers may be disjoint.

An equivalent stronger interface is contextwise saturation and alignment,

```text
sum_T Q_(c,T) S_D8=S_D8+o(1)             for every c, (SMC19)
```

together with agreement of the shared-variable compressions on those
carriers.  Equations `(SMC18)` or `(SMC19)` are the exact remaining
promotion step.  Truth-table computation, role orientation, external
multiplicity action, normalization, and exact allowed-sector extension no
longer enter that axiom.

Gauge doubling is compatible with the construction: replace the assignment
label `x` by its two-share label `(a,b)` and use `f(ab)` in `(SMC7)`.  The
simultaneous share flips permute `Omega`, so the exact gauge-orbit
covariantization extends.  The equal-scale derived lift can transport the
selected type to the next packet.  Neither operation is needed to cancel
`[R,T]`; that cancellation occurs in `(SMC4)`.

The construction is also compatible with
`centralizing-d8-word-anchors-relative-row-orientation`.  That anchor rules
out multiplication of a selected row by the wrong relative role bit while
leaving a common whole-row operator free.  Equation `(SMC15)` has exactly
that permitted form.  Thus absolute relative orientation and nonlinear row
evaluation no longer compete for a scalar multiplicity character.

## Attempts and firewalls

- **Cancel `[R,T]` with an additional relator.**  Unnecessary, and after full
  cancellation the row would hit the universal finite-packet obstruction if
  one also claimed source saturation.
- **Omit the inert duplicate.**  A diagonal sign with odd determinant cannot
  be a finite-dimensional commutator.  Duplication is the fixed equal-scale
  determinant repair.
- **Use different multiplicity factors on the two roles.**  Then `(SMC4)`
  leaves their ratio and the construction fails.  The complete covariance
  table on one irreducible role packet is what supplies one common factor.
- **Claim global BCS groupification.**  The local row is solved only on its
  selected isotypic carrier.  A common-source or coherent-return theorem is
  still required before the finite game gap can sum all context rows.
