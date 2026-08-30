---
rg: 2
id: whitehead-universal-group-via-effective-hnn-and-rope
kind: route
title: Make the countable free product two-generated without losing Whitehead classes
target: whitehead-universal-finitely-presented-torsion-free-group
requires: [torsion-free-universal-quotient-recursively-presented, amalgam-torsion-permanence-needs-no-cyclic-reduction, hnn-torsion-theorem, waldhausen-hnn-vertex-whitehead-injectivity, whitehead-injective-torsion-free-embedding]
---

## 1. A recursive torsion-free free product containing every finite input

Effectively enumerate all finite presentations P_1,P_2,... . Apply Chiodo's
universal torsion-free quotient algorithm (arXiv:1107.1489, Proposition 3.8)
to each P_i and call the resulting finitely generated recursively presented
torsion-free group T_i. If P_i already presents a torsion-free group, the
universal quotient map is an isomorphism. Therefore

    Q = *_(i>=1) T_i

is a countably generated recursively presented torsion-free group in which
every finitely presented torsion-free group occurs as a free factor. Each
factor inclusion is split by the retraction killing all other factors, so it
is split-injective on Whitehead groups.

## 2. The effective two-generator HNN host

Choose a recursive presentation Q=<q_1,q_2,... | R> and put

    V = Q * F(a,b).

Inside V define

    A = < b, q_i a^(-i) b a^i : i>=1 >,
    B = < a, b^(-i) a b^i       : i>=1 >.

The displayed sets are free bases. For B this is the standard conjugate basis
inside F(a,b). For A, the retraction V->F(a,b) killing Q sends its displayed
generators to the free set {b,a^(-i)ba^i}; hence a nontrivial reduced word in
the displayed A-generators cannot vanish. Thus the basis-to-basis map is an
isomorphism A->B.

Form the single HNN extension

    E = < V,t |
          t^(-1) b t = a,
          t^(-1)(q_i a^(-i)b a^i)t = b^(-i)a b^i, i>=1 >.

This is the standard effective Higman--Neumann--Neumann embedding; compare
Morozov--Schupp, Computable permutations and word problems, L'Enseignement
Mathematique 64 (2018), Observation 3.4,
DOI 10.4171/LEM/64-1/2-6.

The relations solve for all old generators:

    b   = t a t^(-1),
    q_i = t b^(-i)a b^i t^(-1) a^(-i)b^(-1)a^i.

Substituting these words into the recursively enumerable set R gives an
explicit two-generator recursively enumerable presentation of E on {a,t}.
Normal form embeds V in E. Since V is torsion-free and an HNN extension has
no torsion outside conjugates of its vertex group, E is torsion-free.

The map Q->V is split. The edge A is a free group, possibly of countably
infinite rank, so Wh(A)=0; for example this follows by writing A as the
directed union of its finite-rank free factors and using Wh(F_n)=0 together
with continuity of K_1. The general Waldhausen HNN fibration now gives an
injection

    Wh(V) -> Wh(E).

Thus Wh(Q)->Wh(E) is injective, and every finitely presented torsion-free
factor G of Q embeds in E Whitehead-injectively.

## 3. One finitely presented host

The group E is two-generated, recursively presented, and torsion-free.
Apply [[whitehead-injective-torsion-free-embedding]] once to obtain a
finitely presented torsion-free U with Wh(E)->Wh(U) injective. Composing the
maps constructed above gives, simultaneously for every finitely presented
torsion-free G,

    Wh(G) -> Wh(Q) -> Wh(V) -> Wh(E) -> Wh(U)

injective.

If Wh(U)=0, all finitely presented torsion-free Whitehead groups vanish. The
established route
[[whitehead-recursively-presented-via-injective-embedding]] then gives
vanishing for finitely generated recursively presented torsion-free groups,
and [[whitehead-global-via-recursively-presented-reduction]] gives the global
conjecture. Conversely, global vanishing applies to U. QED

The index i>=1 is essential: starting at zero would duplicate the first
basis generator and destroy the displayed basis-to-basis isomorphism.
