---
rg: 2
id: one-sided-pvm-leakage-controls-schreier-multiplicity
kind: claim
title: One-sided actor leakage controls the square-root multiplicity Dirichlet energy
distinct_from:
  infinite-schreier-pvm-transport-kills-finite-mark: that starts from the two-sided Hilbert--Schmidt transport energy of projections; this proves the sharper interface directly from one-sided off-target block leakage.
  finite-covariance-energy-sees-only-character-restrictions: that proves finite lamp-word tests do not recover fine global character transport; this lemma starts only after one exact globally indexed PVM and its one-sided leakage have actually been decoded.
  global-schreier-pvm-is-stronger-than-action-soficity: that separates a global equivariant PVM from an approximate action; this isolates the elementary multiplicity inequality and its exact constant.
---

**ESTABLISHED SELF-CONTAINED ATOMIC SCHREIER LEMMA.**  Let `Omega` be an
invariant countable set for a finite actor set `S`.  Let `(Q_chi)` be an
exact finite-support spectral PVM in a finite tracial matrix algebra, put

```text
q_chi=tau(Q_chi),                 f_chi=sqrt(q_chi),   (ASL1)
```

and let `U_s` be an arbitrary actor unitary.  Define its one-sided leakage
from the prescribed character transport by

```text
L_s=sum_(chi in Omega)||(1-Q_(s chi))U_sQ_chi||_2^2.  (ASL2)
```

Then, with `(s f)(s chi)=f(chi)`,

```text
||f-sf||_(ell^2(Omega))^2 <= 2L_s.                    (ASL3)
```

Consequently, if the Schreier action has the uniform finite-support gap

```text
kappa||g||_2^2 <= sum_(s in S)||g-sg||_2^2,           (ASL4)
```

then the total multiplicity mass satisfies

```text
mass(Omega)=sum_(chi in Omega)q_chi
             <=(2/kappa)sum_(s in S)L_s.              (ASL5)
```

The estimate uses neither Property `(T)` nor a representation-stability
input.  It is a projection overlap calculation followed by the stated
scalar Schreier gap.

**Conditional regular-lamp consequence.**  Let an actor group act on a
regular `C_2`-lamp module, and suppose a finite matrix model has already
been decoded to one exact, globally indexed lamp spectral PVM on a marked
carrier.  Suppose also that:

1. all character mass forced by the chosen one-lamp/two-lamp marked packet
   lies in an invariant union `Omega` of proper-stabilizer orbits;
2. one fixed finite actor set has gap at least `kappa>0` on the direct sum
   of all those Schreier orbits;
3. the marked packet forces `mass(Omega)>=c mu`, where `mu` is the marked
   carrier mass and `c>0` is independent of matrix dimension; and
4. the decoded actor-word defects bound the one-sided leakages `(ASL2)`.

Then

```text
mu <=(2/(c kappa))sum_(s in S)L_s.                    (ASL6)
```

Thus vanishing decoded leakage collapses the regular-lamp/two-lamp mark.
This corollary is deliberately conditional.  The lemma does **not** decode
one global PVM from bounded local lamp windows, does not prove a uniform gap
for every proper stabilizer, and does not turn a classical LTC into the
operator-valued/global-PVM decoder.  Finite covariance tests can remain
blind inside character-restriction fibers, exactly as recorded by
`finite-covariance-energy-sees-only-character-restrictions`.  Those are the
remaining gates; `(ASL3)--(ASL5)` do not bypass them.

No Property `(T)`, Kazhdan input, literature theorem, local computation, or
Lean compilation is used.

DERIVATION
atomic-schreier-multiplicity-leakage-proof
