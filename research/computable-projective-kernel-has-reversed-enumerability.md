---
rg: 2
id: computable-projective-kernel-has-reversed-enumerability
kind: claim
title: A computable character exposes the complement of its projective kernel, not the relator kernel
distinct_from:
  mipstar-does-not-supply-effective-projective-basis: that audits the cited game constructions and records that they supply neither a projective basis nor an effective scalar kernel; this is the recursion-theoretic theorem explaining why computability of character values alone has the wrong enumeration polarity.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that proves the raw projective kernel loses finite-dimensional soundness; this separately proves that even an effective non-CE character need not supply the r.e. equalities required by a recursive presentation.
  diagonal-tensor-trace-powers-forget-full-gns-tensor: that identifies the operator-algebra retention failure under tensor powers; this also identifies the independent effectivity failure of the limiting scalar kernel.
---

Let `F` be a finite-rank free group and let `tau:F->C` be a uniformly
computable character.  Its projective GNS kernel

```text
K_tau={w in F: |tau(w)|=1}
```

is **co-c.e.**  Consequently, if `K_tau` is also recursively enumerable, then
it is decidable.  Computability of the character therefore does not supply
the r.e. normal kernel needed by `effective-nonce-twisted-factor-exists`; it
semidecides exactly the opposite, non-scalar side.

The obstruction remains after balanced diagonal tensor polarization.  The
characters

```text
psi_n(w)=|tau(w)|^(2n)
```

converge pointwise to `1_(K_tau)`, but testing whether the limit is `1` means
verifying all precision tests and is again a co-c.e. condition.  A recursive
nonce schedule can discover and label every non-scalar word at a finite
stage; it cannot enumerate the scalar equalities unless the projective word
problem is already decidable.

There is a second, independent obstruction even when the kernel happens to
be decidable.  Centralizing `K_tau` selects the canonical twisted regular
trace

```text
tau_reg^chi(w)=chi(w),  w in K_tau,
                 0,    w notin K_tau,
```

on the projective quotient.  It does not select `tau`.  Thus the construction
retains the non-Connes-embeddable payload exactly when this twisted regular
factor is itself non-CE, which is the original effective twisted-factor gate.

The separation is sharp.  Start with the finitely presented hyperlinear RACG
carrying the known non-CE BCS character `tau_0`, and mix it with its regular
character:

```text
tau_epsilon=(1-epsilon)tau_0+epsilon tau_reg,
0<epsilon<<1.
```

The Connes-embeddable trace locus is closed, so every sufficiently small
positive `epsilon` leaves `tau_epsilon` non-CE.  On the group its scalar
kernel is trivial, because the regular summand has coefficient zero at every
nonidentity element.  Pulled back to a finite free presentation, the scalar
kernel is therefore just the ordinary relator kernel, which is decidable for
a RACG.  Nevertheless the associated untwisted regular factor is `L(G)`,
which is CE because the RACG is hyperlinear.  Hence even a decidable scalar
kernel plus a non-CE payload character does not give the required bad
twisted regular sector.

The exact surviving target for any recursive diagonal/free-label proposal is
therefore a **retention theorem**: the algebra generated in the limiting
projective-regular GNS representation must contain a trace-preserving non-CE
corner or quotient.  Merely having the payload in the ambient full tensor
product is insufficient, and adding cancellable free labels restores payload
moments while destroying projective regularity.
