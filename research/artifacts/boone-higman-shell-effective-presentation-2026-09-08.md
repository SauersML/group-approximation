# Effective information forced by a shell presentation, 2026-09-08

The universal shell-stabilizer construction remains open. This step
shows that a successful enumeration cannot hide noncomputable data,
and states exactly which algorithms a proposed presentation would supply.

## Recovering the enumeration

Let v_n flip the first suffix bit inside shell C_n and fix everything
else. Mark v_0,v_1 and the prefix element t with table
0->00, 10->01, 11->1. Then v_n=t^(n-1)*v_1*t^(-(n-1)) for n>=1.
For every input word g,

    hat(g)*v_n*hat(g)^-1=v_(rho_g(n)).

A correct recursive presentation of E_nu or A_1 enumerates these
equalities. Searching simultaneously for their right-hand sides
computes every rho_g(n), because exactly one answer exists. The
free even-index action decides whether g=1 by whether rho_g(0)=0.
With the fixed integer n_0=nu(1_P), it also computes
nu(g)=rho_g(2*n_0)/2. Inverse word representatives follow by search.

The required presentation and finitely many marked words are assumed
correct. This does not give a test for the correctness of a proposed
presentation, a method to find a successful presentation, or a runtime
bound. Nonetheless it proves that any successful enumeration is itself
computable. The universal open claim can require computability of nu
without becoming stronger; uniform construction from P alone remains
unproved.

The same marked equalities determine nu even in a fixed abstract
countable group without computable operations. There are only countably
many choices of the finite marking and n_0, so each abstract group occurs
for at most countably many enumerations. Both E_nu and A_1 therefore
range over continuum many isomorphism classes for any fixed infinite
finitely generated P.

## The ambient word problem

For a finite puncture set F, the group K_F of prefix elements equal
to the identity near F is a nested union of copies of V, hence simple.
Every nontrivial normal subgroup of any Cantor homeomorphism group
containing K_F contains K_F: displace a small cone away from F and
use the double commutator from the existing prefix-kernel proof.

Fix 1!=k in K_F. In a recursive presentation, dovetail a proof of
w=1 with a proof of k=1 after adding w as a relator. Exactly one
search succeeds. Thus recursive presentations of E_nu or the finitely
generated shell singularity stabilizers also decide their own word
problems. This argument cannot be transferred to Q: the germ quotient
kills the chosen discriminator k.

## Finite agreement does not certify these properties

A finite relabeling of nu is implemented by a finite permutation of
even shells, whose lift belongs to V. It leaves the actual E_nu and
all S(M,M') unchanged. The virtually cyclic positive enumeration
can therefore be altered to meet any finite injective prescription.
It still gives finitely presented shell groups and stabilizers.

Every such prescription also has noncomputable extensions. The
extraction algorithm rules out even an abstract recursive presentation
of their E_nu and A_1. Thus finite samples can agree with both the
positive construction and groups that are not recursively presentable.
For the virtually cyclic family the finite-presentation locus is
countable and dense; the non-recursively-presentable locus is dense
and comeagre. This concerns finite point samples, not finite proofs
about an entire enumeration formula.

## Finite generation of point stabilizers is automatic

The independent-germ argument supplies more than an obstruction.
For all finite M subset F subset Omega, the joint germ map of
S(M,F) surjects onto the product of Q_x at singular points and
cyclic prefix germs at the other points. To prescribe a germ at
one point, take its one-singularity representative and cancel its
prefix germs near the other points by a finite V correction.

The product is finitely generated whenever P is. Its neighborhood
kernel lies in the finitely generated prefix stabilizer Fix_V(F).
Lifts of finitely many germ generators together with generators of
Fix_V(F) therefore generate S(M,F). Applying the finite-germ theorem
at n=1 to E_F proves that every finite point stabilizer of E_nu is
finitely generated, for every enumeration of every finitely generated P.

This yields the shorter route `boone-higman-via-fp-shell-envelopes`.
It only needs a finitely presented E_nu: its action already meets
the point-stabilizer requirement of the twisted Brin--Thompson
construction. The three stronger stabilizer clauses remain one
sufficient way to prove E_nu finitely presented. Their necessary
germ and ascending HNN conditions have not been shown necessary
for this shorter route. In particular, Q need not be assumed
finitely presented in the new open envelope hypothesis.

## Remaining work and verification boundary

The previous fiber-product and ascending HNN tests concern the germ
quotient. This record adds an effective restriction on any successful
envelope presentation and removes the point-stabilizer finite-generation
condition as a separate construction problem. It does not show that
the germ tests suffice, nor construct a successful enumeration for
arbitrary decidable P.
No example with finitely presented Q but non-recursively-presentable
A_1 has been constructed here; the implications have not been reversed.

These are written proofs in Cairn. Remote structural checks will
validate the graph wiring, not formally verify the mathematics.
No GPU ran, no local code or build was executed, and no Civo resource
was created for this step. The conjecture remains open.
