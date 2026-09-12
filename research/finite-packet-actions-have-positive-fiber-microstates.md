---
rg: 2
id: finite-packet-actions-have-positive-fiber-microstates
kind: claim
title: Finite packet actions induce canonical actor microstates with every nonzero packet fiber positive
distinct_from:
  finite-overgroup-packing-preserves-hyperlinearity: that treats Bass--Serre attachment of finite overgroups along finite edges; this treats noncommuting covariance relations in a finite semidirect action on the actor itself and tracks a protected packet projection.
  hyperlinear-fiber-cannot-orient-btb-return: that assumes an active multiplicity presentation has approximate models and adds an invariant spectator half; this constructs the crossed active models explicitly and uses the full prescribed packet fiber rather than an arbitrary reducing subprojection.
  ordinary-leavitt-quotient-fences-whitehead-active-floor: that gives one concrete quotient graft conditional on hyperlinearity of an ordinary Leavitt group; this proves the general absorption theorem for every finite automorphism coupling of any hyperlinear actor.
  independent-address-capacity-cannot-drive-selected-atom-growth: that gives a trace-capacity inequality for an independent address tensor factor; this permits the packet to act nontrivially on the actor and absorbs that coupling by finite regular induction.
---

**ESTABLISHED FINITE-ACTION ABSORPTION.**  Let `K` be a countable
hyperlinear group, let `P` be finite, and let

```text
alpha:P -> Aut(K),             G=K rtimes_alpha P.      (FPA1)
```

Then `G` has canonical microstates in which every nonzero projection
`F in C[P]` has its normalized regular packet trace

```text
tau_G(F)=tr_reg,P(F)>0.                                (FPA2)
```

In particular this remains true when `F` is a Reynolds/sign projection of a
finite subgroup of `P`.

There is an explicit microstate construction.  Given a sufficiently accurate
canonical actor microstate `theta:K -> U(d)` on the finite union of all
`P`-translates of the required word window, act on

```text
H_theta=l^2(P) tensor C^d.                             (FPA3)
```

The packet acts by its left regular permutation on the first factor.  On the
block indexed by `p`, let `k in K` act by

```text
theta(alpha_(p^(-1))(k)).                              (FPA4)
```

With the consistent right/left convention, block permutation gives

```text
rho(q)rho(k)rho(q)^*=rho(alpha_q(k))                   (FPA5)
```

up to exactly the actor multiplication defects already present in `theta`.
Every word defect of `rho` is the average of finitely many defects of `theta`
on automorphic images, so it tends to zero dimension-independently.

The normalized trace is canonical.  A word `kq`, `q!=1`, permutes the
`P`-blocks without fixed points and has trace zero.  For `q=1` and `k!=1`,
its trace is the average over `p` of
`tr_d(theta(alpha_(p^(-1))(k)))`, which tends to zero.  On `C[P]` the model
is the regular representation with multiplicity `d`, proving `(FPA2)`.
Every nontrivial marked actor word remains at canonical squared distance two
from the identity.

The same conclusion holds for finite-valued projective covariance after
replacing `P` by the corresponding finite central extension, and for a fixed
finite collection of packet types after taking their finite direct sum.

Now tensor `(FPA3)` with any exact outer BCS/BTB structural model containing
a positive forbidden atom `A`; let the proposed protected active fiber be

```text
F_act=A tensor F.                                      (FPA6)
```

Then `tau(F_act)=tau(A)tr_reg,P(F)>0`.  Every actor, packet, and crossed
covariance relator has vanishing defect, hence so does its compression to
`F_act`.  Therefore no inequality

```text
sum_r ||(rho(r)-1)F_act||_2^2
   >= kappa tau(F_act)-o(1),             kappa>0        (FPA7)
```

can follow from a finite action/covariance presentation when `K` is
hyperlinear.

This is stronger than independent tensor absorption: the packet letters in
`(FPA5)` genuinely do not commute with the actor.  Finite automorphism
coupling, finite projective phases, and finite occurrence-orbit replication
all survive by regular induction.

**Boundary.**  A relation capable of proving the protected-fiber floor must
make the positive-fiber specialization leave this class.  It cannot merely
conjugate actor generators by a finite control packet.  It must impose a
global coefficient/holonomy relation whose active specialization is not a
finite extension of the actor, use a noninvertible proper-corner incidence
which is not group-conjugacy covariance, or else prove that the actor itself
is nonhyperlinear.  In each case the failure of `(FPA3)--(FPA5)` must be the
same relation that pays the desired floor.

DERIVATION
induce-actor-microstates-across-finite-packet-action
