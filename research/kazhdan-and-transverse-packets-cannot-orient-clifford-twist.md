---
rg: 2
id: kazhdan-and-transverse-packets-cannot-orient-clifford-twist
kind: claim
title: Kazhdan actors and fixed transverse packets cannot orient a Clifford multiplicity twist
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that identifies the arbitrary factor in one Clifford implementer; this proves that actor expansion and any fixed transverse packet leave that factor completely free after spectator amplification.
  normalizer-multiplicity-twist-breaks-prefix-expander-rounding: that gives a correlated spin-multiplicity invariant vector defeating a Clifford quantum expander; this gives a simpler exact countermodel even when the actor representation is irreducible and has a Kazhdan gap.
  pure-prefix-swap-invariants-are-selector-blind: that rules out invariants of the prefix word itself; this rules out the proposed mixed coupling to an external actor or a second packet.
---

**ESTABLISHED NO-GO.**  On a selected Pauli spin carrier, a Clifford
implementer has the form

```text
t=C tensor V,                                            (KCT1)
```

where `C` is the desired fixed Clifford matrix and `V` acts on the external
multiplicity space.  Neither a nonamenable/property-`(T)` actor coupled by
covariance nor any fixed family of transverse finite packets can force
`V ~= I` with a dimension-uniform normalized-HS estimate.

## Exact spectator-sign countermodel

Let `pi:A->U(M)` be any exact finite-dimensional actor representation and
suppose `V_0` implements an actor automorphism `alpha`:

```text
V_0 pi(a) V_0^*=pi(alpha(a)).                           (KCT2)
```

The commuting case is `alpha=id`.  For every `r,s>=0`, put

```text
D_(r,s)=diag(I_r,-I_s),
pi_(r,s)(a)=pi(a) tensor I_(r+s),
V_(r,s)=V_0 tensor D_(r,s).                            (KCT3)
```

Then `(KCT2)` remains exact with `pi_(r,s),V_(r,s)`.  The same is true for
every relation which uses the Clifford letter only through conjugation,
commutators, or a full covariance table.  If `V_0^2=1`, then
`V_(r,s)^2=1` as well.  Nevertheless

```text
tr(D_(r,s))=(r-s)/(r+s),
||D_(r,s)-I||_2^2=4s/(r+s).                            (KCT4)
```

Thus zero actor/covariance defect coexists with every rational twist moment
in `[-1,1]` and every rational orientation error in `[0,4]`.

This countermodel is already present when `pi` is irreducible.  Irreducibility
only makes the original commutant scalar; common amplification replaces it
by `I_M tensor M_(r+s)`, which contains `(KCT3)`.  Direct-sum closure makes
that amplification unavoidable in finite-dimensional representation theory.

## Why property `(T)` does not improve the conclusion

For a Kazhdan generating set `S`, the available estimate has the form

```text
dist(V,pi(A)')^2
 <=kappa^(-2) sum_(a in S)||[V,pi(a)]||_2^2.            (KCT5)
```

Every spectator sign in `(KCT3)` belongs to `pi_(r,s)(A)'`.  Hence both
sides relevant to commutant capture are zero while `||V-I||_2` is arbitrary.
Property `(T)` resolves off-isotypic transport; it does not choose an
orientation inside an isotypic multiplicity algebra.  Nonamenability alone
provides still less control.

The same calculation covers finitely many actor packets simultaneously:
tensor their joint exact representation with `I_(r+s)`.  Even if their
fixed label algebras generate a full matrix algebra, their common commutant
after amplification contains the full spectator factor.

## A second finite packet has the same escape

Let `B_1,...,B_k` be any fixed finite transverse packets, represented
jointly on a fixed label space `L`.  On

```text
L tensor C^(r+s)                                        (KCT6)
```

represent every packet word as its label matrix tensored with `I_(r+s)` and
put the Clifford twist in the second factor as `D_(r,s)`.  All packet tables,
cross-commutators, and covariance rows remain exact.  Finite-group flexible
HS exactification therefore cannot remove this model: it is already exact.

In particular, for the desired literal fine reflection `C`,

```text
Re tr((C tensor I)^*(C tensor D_(r,s)))=tr(D_(r,s)),    (KCT7)
```

so the mixed selector moment itself ranges over `[-1,1]` at zero defect.
A fixed transverse packet can fingerprint the label factor, but cannot
authenticate ownership of the anonymous spectator multiplicity factor.

## The necessary escape is phase-sensitive, not another covariance row

Every conjugation presentation is invariant under the scalar sign change
`t |-> -t`.  More generally, any relator in which the total exponent of `t`
is even has identical defect on the two orientations.  Taking direct sums of
the two orientations gives `(KCT3)`.  Therefore a successful coupling must
contain a phase-sensitive two-cell which is not invariant under this sign,
or must make the twist the value of an actor element which is robustly
trivial in all approximate finite-dimensional representations.

The latter alternative is not supplied by property `(T)`.  Exact
finite-dimensional invisibility plus a dimension-uniform approximate
trivialization modulus is a marked HS-stability statement.  If such an actor
were hyperlinear, stability would force the relevant finite-dimensional
residual separation; in the invisible case it is already a nonhyperlinearity
engine independent of the Clifford cell.  Thus importing it here merely
moves the main obstruction into the actor.

Finally, imposing the odd-orientation identity universally on the selected
coarse/fine carrier is not an escape: the quarter-trace selector-covariance
floor then holds in the regular finite trace and kills that carrier.  The
remaining viable target is necessarily a genuinely matrix-only,
phase-sensitive coupling tied to the payload, not an actor commutant gap or
a fixed transverse packet.
