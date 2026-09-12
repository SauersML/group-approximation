---
rg: 2
id: certificate-routing-bernoulli-balance-proof
kind: route
title: Count incoming reads under Bernoulli certificates and use locality to detect every defect
target: certificate-controlled-routing-is-surjunctive
requires: []
---

## Conventions and the certificate fibers

Use the left shift (h.c)(g)=c(h^(-1)g). Equivariance of the routing means
phi_(h.c)(hg,i)=h.phi_c(g,i), with h acting on the group coordinate only.
There is a finite D subset G such that phi_c(g,i)=(gd,j) for d in D.
Its choice at (g,i) depends on c restricted to gM for one finite M.
This is exactly the locality used below; no group approximation is used.

For a fixed certificate c, the data map is pullback along phi_c.
It is injective exactly when phi_c is onto: an unread input coordinate
can be changed invisibly, whereas reading every coordinate recovers x.
It is onto exactly when phi_c is injective: distinct reads of the same
coordinate constrain the two output symbols, whereas distinct input
coordinates can be assigned their requested symbols independently.

Keeping c in the output makes these fiberwise criteria equivalent to the
corresponding global criteria for E. Applying permutations of A to the
read symbols changes neither criterion: duplicated reads still constrain
the output pair to |A| possibilities instead of |A|^2.

## Incoming reads have the same expected total as outgoing reads

Give B^G its iid uniform probability measure mu. Write

    N_j(c) = #{(g,i): phi_c(g,i)=(1,j)}.

Only g in D^(-1) contribute, so these are finite, locally determined
nonnegative integers. By equivariance and shift invariance of mu,

    E N_j = sum_(i,d in D) mu{phi_c(d^(-1),i)=(1,j)}
          = sum_(i,d in D) mu{phi_c(1,i)=(d,j)}.

Summing over j gives sum_j E N_j=r: each of the r output coordinates
at the identity chooses exactly one input coordinate.

If E is injective, every phi_c is onto, so every N_j(c)>=1.
The expectation identity forces every N_j=1 almost surely. The event
N_j>=2 is determined by finitely many certificate coordinates. Any
nonempty such event contains a cylinder of positive mu-measure.
Consequently it is empty, not merely null. Equivariance now gives
indegree one at every site for every certificate. Each phi_c is bijective,
so E is surjective.

Conversely, if E is surjective, every N_j(c)<=1. The same expectation
identity forces N_j=1 almost surely, and locality excludes N_j=0 anywhere.
Thus E is injective as well. This argument does not require countably many
sites: it transfers an identity-site local statement using equivariance.

## A finite witness to corrupted routing

For r=1, E N=1 and the pointwise identity

    N-1 = (N-1)_+ - 1_(N=0)

give mu{N=0}=E[(N-1)_+]. If any certificate has N>=2, its restriction
to F=union_(d in D) d^(-1)M witnesses that event. Hence, writing b=|B|,

    mu{N=0} >= mu{N>=2} >= b^(-|F|).

There must be a certificate with an unread identity coordinate, and
changing only that input datum gives an explicit type of collision for E.
The bound concerns certificate probability, not Hilbert--Schmidt error.
For multiple tracks the corresponding balance is

    sum_j mu{N_j=0} = sum_j E[(N_j-1)_+].

## Finite circuits cannot hide a lossy stage

Let T=T_m ... T_1 on one full shift, each stage either one of the routing
rules above or a reversible cellular automaton. Each stage has the
property that injectivity implies bijectivity. If T is injective, T_1 is
injective and therefore bijective. Cancelling this bijection shows
T_m ... T_2 is injective. Induction makes every stage bijective and T
surjective. This permits reversible stages that mix data and certificate
tracks and changes of the decomposition used by later routing stages.

A simultaneous constraint network or a more general irreversible local
mixing rule need not have this factorization. The argument supplies no
claim about those possibilities. A strict embedding defined only on valid
certificates also evades the proof because the iid measure need not be
supported on that certificate subshift.

The underlying mean-one argument is the discrete instance of the standard
mass-transport test for bijective point-shifts; see Proposition 2.2(j) in
Murphy, https://arxiv.org/abs/1704.08333. The proof here is self-contained
and upgrades almost-sure balance to all certificates using finite memory.
