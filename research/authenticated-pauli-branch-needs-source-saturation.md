---
rg: 2
id: authenticated-pauli-branch-needs-source-saturation
kind: claim
title: An authenticated Pauli branch is stationary until both children saturate the same source
distinct_from:
  mixed-pauli-commutator-authenticates-one-capacity-cut: that identifies the leakage energy with one authenticated root involution; this tests whether survival of that involution alone supplies a binary multiplicity recurrence.
  pauli-two-child-transfer-packet: that constructs one exact equal-trace branch in the atlas packet; this gives the abstract scalar recurrence, an exact stationary Pauli countermodel, and the universal-trace firewall for iterating the branch.
  approximate-relative-leavitt-cell-kills-active-trace: that uses decoded two-sided Leavitt inverse and range-sum relations to kill a projection; this isolates the weaker two scalar source-saturation moments needed for one branching step.
---

Let `Y=[X_1,Z_1]` be the authenticated involution from
`mixed-pauli-commutator-authenticates-one-capacity-cut`, and put

```text
P=(I-Y)/2.                                               (APB1)
```

The slogan

```text
Y survives and has two orthogonal children carrying Y
```

does not imply a contractive multiplicity recurrence.  The smallest exact
Pauli packet already gives a canonical stationary countermodel.  The missing
hypothesis is that **each** child map use the whole parent as its source, not
merely that the two child projections partition the parent.

## Exact stationary Pauli countermodel

Let `E_2` be the two-pair extraspecial group

```text
E_2=<Y,X_1,Z_1,X_2,Z_2 |
     Y central, all generators involutions,
     [X_i,Z_i]=Y,
     distinct pairs commute>.                           (APB2)
```

In its left regular representation define

```text
P_+=P(I+X_2)/2,
P_-=P(I-X_2)/2.                                         (APB3)
```

Then exactly

```text
P_+P_-=0,
P_++P_-=P,                                              (APB4)
```

and both `P_+` and `P_-` reduce `X_1,Z_1,Y`.  On each
nonzero child, the same authenticated relation remains true:

```text
[X_1,Z_1]=Y,
Y P_+=-P_+,
Y P_-=-P_-.                                             (APB5)
```

The normalized regular trace is

```text
tau(P)=1/2,
tau(P_+)=tau(P_-)=1/4.                                  (APB6)
```

Indeed every nonidentity group element has regular trace zero, and expansion
of `(APB1)--(APB3)` gives `(APB6)`.

Consequently the proposed zero-error recurrence

```text
mu_parent <=(mu_++mu_-)/2                               (APB7)
```

fails maximally:

```text
1/2 not<=1/4.                                           (APB8)
```

This model already has the authenticated `Y`, canonical packet trace, two
orthogonal children, and exact inheritance of the parent Pauli relations.
The children merely **partition** the parent.  Neither one is a full
multiplicity copy of it.

## Exact one-step recurrence from source saturation

The missing scalar is elementary and dimension-free.

### Theorem

Let `(M,tau)` be a finite tracial von Neumann algebra.  Let `P,B_0,B_1` be
projections with `B_0B_1=0`, and let `S_0,S_1` be contractions.  Put

```text
alpha_i=||S_i^*S_i-P||_2,
lambda_i=||(I-B_i)S_i||_2.                              (APB9)
```

Then

```text
tau(P)
 <=[tau(B_0)+tau(B_1)]/2
   +(alpha_0+alpha_1+lambda_0^2+lambda_1^2)/2.           (APB10)
```

In particular, exact full-source arrows

```text
S_i^*S_i=P,
S_iS_i^*<=B_i,
B_0B_1=0                                                (APB11)
```

give

```text
tau(P)<=[tau(B_0)+tau(B_1)]/2.                          (APB12)
```

### Proof

For each `i`, traciality and Cauchy--Schwarz give

```text
tau(P)
 <=tau(S_i^*S_i)+alpha_i
 =||S_i||_2^2+alpha_i.                                  (APB13)
```

The two left components of `S_i` are orthogonal, so

```text
||S_i||_2^2
 =||B_iS_i||_2^2+||(I-B_i)S_i||_2^2
 <=tau(B_i)+lambda_i^2,                                 (APB14)
```

where the last inequality uses `S_iS_i^*<=I`.  Add `(APB13)--(APB14)` for
`i=0,1` and divide by two.  This is `(APB10)`.  ∎

Thus no operator-valued equality `S_i^*S_i=P` is logically needed for the
scalar recurrence.  The weakest input is two lower source moments

```text
tau(S_i^*S_i)>=tau(P)-e_i                               (APB15)
```

plus range leakage into orthogonal `B_i`.  This is strictly smaller than a
full Leavitt decoder.

In the stationary packet `(APB3)`, the obvious child compressions have
source Grams `P_+` and `P_-`, not `P`.  Each misses exactly trace `1/4` of
the parent.  Equation `(APB10)` therefore identifies, rather than hides, the
escape.

## Exact Hilbert-hotel completion

The saturated cell has a completely explicit nontracial infinite model.
On

```text
H=C^2 tensor ell^2(N),
```

take

```text
X_1=sigma_x tensor I,
Z_1=sigma_z tensor I,
Y=-I,
P=I.                                                    (APB16)
```

Let `s_0 e_n=e_(2n)` and `s_1 e_n=e_(2n+1)` be the two Cuntz isometries on
`ell^2(N)`, and put

```text
S_i=I tensor s_i,
B_i=S_iS_i^*.                                           (APB17)
```

Then

```text
S_i^*S_i=P,
B_0B_1=0,
B_0+B_1=P,                                              (APB18)
```

and both branches commute with and retain the authenticated Pauli pair.
This is the desired exact Hilbert-hotel completion.  It carries no finite
normalized trace on `B(H)`, so `(APB12)` does not apply.

The HALT firewall is also immediate: when the capacity carrier is zero,
take `P=S_i=B_i=0`; no condition is imposed on the surviving HALT
representation.

## Universal tracial-return firewall

The model `(APB16)--(APB18)` cannot be imposed functorially inside the group
von Neumann algebra of the final group.  If the same exact relations lived in
any finite tracial algebra and returned under the parent budget

```text
B_0+B_1<=P,                                             (APB19)
```

then `(APB12)` would give

```text
tau(P)<=tau(P)/2,
```

so `P=0`.  For `P=(I-Y)/2`, this gives `Y=I`.  Applied to the faithful left
regular representation, it would collapse the mark algebraically.

Therefore the branch maps in a group proof must be decoded only on the
finite-dimensional **multiplicity coordinates** of a fixed packet.  In the
properly infinite exact witness those multiplicity coordinates are infinite
Hilbert spaces and admit `(APB17)`; they must not be universal projections
and partial isometries in the tracial group algebra.

## Finite packets and Bass--Serre edges cannot supply the missing moment

A finite packet alone cannot enforce finite-dimensional disappearance of a
nontrivial `Y`: its left regular representation is a faithful finite matrix
representation.  More generally, a finite graph of finite packet groups is
virtually free and residually finite; its edge restriction multiplicities
have positive stationary integer flows.  The regular `E_2` split
`(APB3)--(APB6)` is the smallest such stationary flow.

Hence a Pauli/Clifford child tag supplies orthogonality and inheritance, but
not the two source moments `(APB15)`.  A finite HNN edge merely redistributes
packet multiplicity among complementary types.

## The extra mixed relation required

After authentication of `Y`, the exact remaining one-step interface is:

```text
two decoded contractions S_0,S_1,
two orthogonal child tags B_0,B_1,
range leakage lambda_0^2+lambda_1^2 paid by word energy,
two scalar source deficits
  tau(P)-tau(S_i^*S_i)
paid by word energy.                                    (APB20)
```

Equation `(APB10)` then gives the requested contractive recurrence.  The
load-bearing word is **both**: one saturated child plus one merely invariant
child leaves the stationary escape alive.

The source deficits in `(APB20)` must be authenticated by a genuinely
infinite, matrix-coordinate actuator--for example a Steinberg boundary or a
nonstationary multiplicity return--without turning `(APB18)` into a universal
tracial identity.  This is the smallest extra mixed relation not present in
the `E_2` countermodel.

## Attempts

- **Use the second Pauli pair as the two children.**  The exact regular model
  `(APB3)--(APB8)` shows that it partitions rather than duplicates the parent.
- **Use the existing Pauli transfer packet.**  It has genuine equal-trace
  source and child projections for one step, but without a matrix-only return
  its finite packet multiplicity graph has a stationary flow.
- **Impose the Cuntz/Leavitt arrows universally.**  The Hilbert-hotel model is
  exact, but `(APB19)` makes the regular finite trace kill `P`, hence the
  group mark.  The decoder must be finite-dimensional-only.
- **Require only child invariance of `Y`.**  Both children in `(APB5)` satisfy
  this exactly while `(APB7)` fails.  Invariance is not source saturation.

## Verdict

The analytic contractive step and its exact infinite completion are both
complete.  The smallest Pauli packet does not realize the step: it has an
exact canonical stationary countermodel.  The one additional datum needed is
two same-parent scalar source-saturation moments `(APB15)`, together with
orthogonal range support.  Making those moments universal collapses the
regular mark, so their group-word realization must be a finite-matrix
multiplicity decoder rather than a tracial Leavitt identity.
