---
rg: 2
id: monomial-central-sign-has-types-or-affine-returns
kind: claim
title: A finite monomial central-sign selector has either multiple marked types or only affine literal returns
distinct_from:
  central-pinning-forbids-nonlinear-predicates: that starts by assuming a unique central-sign irreducible and computes its character; this identifies exactly why a transitive monomial orbit does not imply uniqueness and classifies the remaining literal group elements.
  finite-selector-gadget-induction-barrier: that proves compatible selector characters survive induction to some marked irreducible; this uses the little-group parametrization to exhibit the stabilizer-type ambiguity even when there is only one character orbit.
  affine-selector-clifford-residual-packet: that positively realizes an affine controlled-Pauli pencil after restriction to the unique extraspecial spin type; this proves that a nontrivial normalizer coset always retains a projective multiplicity gauge across all central-sign representations.
  schur-child-center-has-finite-monomial-sector: that realizes the nonlinear corrected child in one chosen irreducible monomial sector; this proves central-sign or character-orbit pinning cannot make that chosen sector universal.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that proves an outer-parity obstruction for repeated copies of one CZ covariance letter; this gives the representation-theoretic source of the arbitrary gauge for every finite normal extraspecial extension.
---

**ESTABLISHED.**  There are two exact finite-group obstructions to using a
central character, or a single orbit of central-sign characters, as the
missing nonlinear child selector.

## Split monomial groups

Let

```text
H=D semidirect K
```

with `D` a finite elementary abelian `2`-group, and let `J in D` be a
`K`-fixed involution.  Put

```text
Omega_-={chi in D^ : chi(J)=-1}.                       (CSM1)
```

For `chi in D^`, write `K_chi` for its stabilizer.  The little-group
classification gives all irreducibles of `H` as

```text
pi_(chi,sigma)=Ind_(D semidirect K_chi)^H(chi tensor sigma),
sigma in Irr(K_chi),                                   (CSM2)
```

up to changing `chi` inside its `K`-orbit, and

```text
pi_(chi,sigma)|_D
  = direct_sum_(eta in K.chi) eta^(direct_sum dim sigma). (CSM3)
```

In particular `pi_(chi,sigma)(J)=-I` exactly when `chi in Omega_-`.
Therefore a **unique orbit** on `Omega_-` is not a unique marked type: for
each `sigma in Irr(K_chi)` it supplies a different `J=-1` irreducible.  If
`K_chi` is nontrivial, there are at least two such `sigma`.

If the central-sign irreducible really is unique, `K` must be transitive on
`Omega_-` and `K_chi` must be trivial.  Thus `K` acts freely and transitively
on `Omega_-`, and the unique irreducible restricts to

```text
direct_sum_(eta in Omega_-) eta.                       (CSM4)
```

This is the full affine hyperplane `eta(J)=-1`, with uniform multiplicity
after restriction to any smaller selector subgroup.

There is a sharper word-level conclusion.  In the induced weight basis a
literal element `h=dk` sends the `eta`-weight space to the `k.eta`-weight
space and multiplies it by the monomial phase contributed by `d`.  Hence,
in the free-transitive case, if `h` preserves every full `D`-weight space,
then `k=1` and `h=d`.  Its sign on that space is

```text
eta |-> eta(d),                                        (CSM5)
```

an affine character of the selector bits.  More generally, `dk` supplies
one selector-independent weight permutation together with this linear
phase; it cannot supply a selector-dependent choice among different Pauli
or root elements.  Thus the two possibilities are exact:

```text
nontrivial little group  -> multiple J=-1 types;
unique J=-1 type         -> only affine literal diagonal returns. (CSM6)
```

*Proof of (CSM2)--(CSM3).*  Since the semidirect product is split and `chi`
is `K_chi`-invariant, `chi` extends to `D semidirect K_chi` by making it
trivial on `K_chi`.  Mackey's little-group theorem gives `(CSM2)`, and the
coset model gives `(CSM3)` directly.  A nontrivial finite group has more
than one irreducible, proving the first alternative.  In the second,
freeness makes a weight-preserving `k` the identity, proving `(CSM5)`.

## Normal extraspecial extensions

Let `E normal H` be an extraspecial `2`-group with center `<J>`, and assume
`J` is central in the finite group `H`.  Let `rho` be the unique spin
irreducible of `E` with `rho(J)=-I`, and put `L=H/E`.  On every `J=-1`
representation of `H`, Clifford theory has the form

```text
pi|_E = rho tensor I_M,
pi(h) = U_(hE) tensor V_(hE)                           (CSM7)
```

after choosing spin implementers `U_l`.  The operators `V_l` form a
projective representation of `L` with multiplier inverse to that of the
`U_l`.  As `pi` ranges over marked irreducibles, the `V`'s range over the
irreducible modules of the corresponding twisted group algebra
`C^alpha[L]`.

No nonidentity `l in L` acts as one prescribed scalar, and in particular as
the identity, in every one of those projective modules.  Indeed, if it did,
the twisted basis element `u_l` would equal that scalar in the faithful
twisted regular representation, impossible because the `u_l` are a basis.
Consequently

```text
pi(h)=U tensor I_M in every J=-1 representation
                  implies h in E.                     (CSM8)
```

This remains true when `C^alpha[L]` is simple: its unique module is faithful,
so a nonidentity twisted basis element still cannot be scalar.

Now take a maximal commuting selector subgroup `A<=E` containing `J`.  An
element of `E` moves an `A`-weight by the fixed commutator character
`a |-> [h,a]`; this translation is independent of the input selector.  If
it preserves every `A`-weight, then

```text
h in C_E(A)=A,                                         (CSM9)
```

and its diagonal phase is again the affine character `eta(h)`.  Thus an
extraspecial packet has the same dichotomy: elements of `E` give fixed
Pauli translations and affine phases, while every genuinely new Clifford,
Hecke, or monomial normalizer letter outside `E` carries the projective
multiplicity gauge `V_l`.

This explains both sides of the existing boundary.  The affine Clifford
packet is valid because it uses packet covariance and later seeks a
same-gauge cancellation; it does not turn an outer Clifford letter into
`U_l tensor I` by central pinning alone.  Conversely, adjoining a nonlinear
diagonal phase such as a higher controlled sign can realize the desired
truth table in one concrete spin model, but the enlarged finite group then
has additional `J=-1` extension types.  The new phase acts as
`U_l tensor V_l`, not as the same corrected child on the entire marked
carrier.  Indeed, the concrete same-spin extension supplies a one-dimensional
projective `V`; its cocycle is therefore a coboundary, so the quotient types
are the ordinary irreducibles of the nontrivial finite group `L`, of which
there is more than one.

## Compiler consequence

The positive monomial construction of `schur-child-center-has-finite-monomial-sector`
is therefore already optimal for a finite central-character selector.  A
nonlinear corrected involution can be literal in one chosen sector.  Making
it universal requires an additional mechanism which selects a little-group
or twisted-quotient type, or cancels its multiplicity gauge with a genuinely
same-reservoir identity-outer anchor.  Neither a unique character orbit nor
the extraspecial central sign performs that job.

## Attempts

The audited proposals were: make `K` transitive on the negative central
characters of a signed monomial diagonal group; use the unique spin type of
an extraspecial group; and adjoin a nonlinear diagonal phase to that spin
packet.  Equations `(CSM2)--(CSM6)` kill the first proposal at the stabilizer
type.  Equations `(CSM7)--(CSM9)` kill the latter two at the twisted quotient
gauge.  The surviving finite construction is explicitly sectorwise, not
central-sign universal, and is already recorded by
`schur-child-center-has-finite-monomial-sector`.
