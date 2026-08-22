---
rg: 2
id: stabilized-morita-branches-are-inner-but-incoherent
kind: claim
title: Two-by-two stabilization internalizes Morita branches but leaves an infinite-stabilizer coherence loss
distinct_from:
  dual-prefix-growth-needs-two-morita-branches: that constructs the two root-dependent monomorphisms and leaves their finite presentation open; this internalizes each monomorphism by one fixed elementary conjugator and identifies the next obstruction.
  conjugate-local-signs-preserve-marked-carrier: that proves local conjugate signs have equal spectral trace; this separates local sign transport from the global common-phase coherence needed by one large Pauli packet.
  bounded-centralizer-fillings-force-finite-stabilizer: that is the general filling theorem; this instantiates it on the stabilized Morita-frame stabilizer and shows why pairwise contextual transports do not give one globally named table.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out changing one finite representation type by conjugacy; here two inner branch restrictions really do grow exact Pauli rank, but their approximate global synchronization remains open.
---

Let `s_i,t_i` be one Leavitt branch, with

```text
t_i s_i=A,          p_i=s_i t_i.
```

In `M_2(B)` define

```text
U_i=[[s_i,A-p_i],[0,t_i]],
V_i=[[t_i,0],[A-p_i,s_i]].                              (SMI1)
```

Then `U_iV_i=V_iU_i=I_2`.  In the three-block Heisenberg group over
`M_2(B)`, put

```text
D_i=diag(I_2,U_i,I_2).
```

Conjugation by `D_i` gives exactly

```text
Ad(D_i) X(aE_11)=X(a t_i E_11),
Ad(D_i) Y(bE_11)=Y(s_i b E_11),
Ad(D_i) Z(cE_11)=Z(cE_11).                              (SMI2)
```

Thus the two Morita branches of
`dual-prefix-growth-needs-two-morita-branches` are restrictions of inner
automorphisms in one fixed stabilization.  Since `GL_2(B)=EL_2(B)`, each
`U_i` is represented by one fixed elementary word; after embedding the
three blocks, no infinitely generated HNN edge relations are needed merely
to name the branches.  Iterated products `D_u` give the exact prefix words
and the full dual-prefix Pauli packet.

This does not yet give a uniform normalized-HS proof from the finite
presentation.  There are two distinct coherence losses.

1. **Common phase.**  Exactly, every `D_i` fixes the outer root
   `J=Z(AE_11)`.  In an approximate tuple, the local sign
   `J_u=D_uJD_u^(-1)` is an exact conjugate and therefore has the same
   spectral trace as `J`, but comparing `J_u` with one globally named `J`
   by telescoping the fixed commutators costs the prefix length.  Local
   conjugate carriers alone do not give the single common phase required by
   the rank-`2^n` divisibility argument.
2. **Pair coherence.**  The full Morita-frame actor is contextually
   transitive on individual prefix frames and on ordered distinct prefix
   pairs: prefix-code units can carry any chosen finite frame to another.
   But a globally chosen transporter for one frame and a pairwise
   transporter differ by an element of the frame stabilizer.  That
   stabilizer is infinite; it contains all prefix permutations supported in
   the complementary cylinder, and it centralizes the local order-`p` root
   packet.  By `bounded-centralizer-fillings-force-finite-stabilizer`, its
   commutators with the local root have unbounded filling area for every
   word section.  Hence contextual diagonal/off-diagonal prototype
   relations cannot be converted into one globally named Pauli table with
   dimension-independent relator area.

Property `(T)` or `(TT)/T` does not automatically remove this loss.  Those
properties act on exact unitary representations or quasi-cocycles for an
exact actor representation.  A matrix microstate supplies only an
approximately multiplicative actor tuple, so its adjoint action is not the
exact representation required by the rigidity theorem.  Same-dimensional
HS exactification of the actor would make a Kazhdan projection available,
but that is precisely another stability hypothesis.

There is also a sharp distinction between **transitivity on the infinite
Morita module** and the finite Pauli-actor hypothesis in
`kazhdan-transitive-pauli-actor-localizes-one-mixed-word`.  Even if the full
elementary actor is transitive on all nonzero unimodular Weyl vectors, it
does not preserve the depth-`n` prefix space: a general elementary
coefficient sends an `E_11`-supported prefix vector outside that finite
packet.  More abstractly, if one fixed group `K` preserves every member of a
properly nested sequence

```text
0 != V_1 < V_2 < ...
```

then it cannot be transitive on the nonzero vectors in their union.  The
orbit of a vector in `V_1` stays in `V_1`.  Consequently a single fixed
actor cannot simultaneously preserve every finite prefix Pauli group and
act transitively on all of its nonzero Weyl vectors.  Restricting to the
setwise stabilizer of `V_n` produces a depth-dependent actor; no uniform
Kazhdan generating set or gap for those stabilizers follows from property
`(T)` of the ambient elementary group.  Averaging over the full infinite
orbit, on the other hand, is not the finite Pauli Reynolds average and does
not yield its exact square-function identity.

This also explains why adding Fourier and shear elements does not yet close
the route.  They can enlarge exact Morita-frame orbits and preserve the
symplectic pairing, but either they leave the finite prefix packet or they
belong to a depth-dependent stabilizer.  Moreover the Gram word must be
approximately invariant under the chosen actor in the *same microstate*.
Property `(T)` converts fixed-generator almost invariance into invariance
only after those generators act by an exact representation; it does not
repair their multiplication table.

Therefore stabilization is a genuine advance: it removes the algebraic
and finite-naming obstruction for each branch.  The surviving target is now
one analytic **global-frame coherence** estimate, simultaneously making the
conjugate local signs common and making contextual pair transports agree
with a global prefix section.  It cannot be supplied by bounded fillings,
and property `(T)/(TT)` supplies it only after actor exactification.  The
conditional gapped-Pauli-actor lemma remains a valid target, but infinite
Morita-module transitivity alone does not instantiate its finite,
uniformly-gapped actor hypothesis.
