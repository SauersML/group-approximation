---
rg: 2
id: automatic-mother-expanders-do-not-normalize-leavitt-prefix-heads
kind: claim
title: Automatic mother-group expanders leave a tail state and do not normalize the Leavitt prefix heads
distinct_from:
  stabilized-morita-branches-are-inner-but-incoherent: that internalizes the two prefix branch maps and isolates finite-packet actor coherence; this tests a concrete odometer/automatic-diagonal mother actor and proves why its level actions do not give compatible inner prefix-head actions.
  truncated-polynomial-binary-weyl-expander-tower: that supplies uniform finite-level projective expanders from relative property T; this supplies a different uniform finite-level linear expander and identifies its exact constant-cost Leavitt compiler failure.
  self-similar-clifford-quantum-expander-tape: that asks for fixed self-similar Clifford word templates; this proves that finite-state level permutations alone are insufficient because their nonconstant sections survive in conjugation of off-diagonal prefix roots.
---

Let `D=2^n`, let `P_n` be the cyclic permutation matrix on `Z/DZ`, and let

```text
D_n=diag(popcount(k) mod 2 : 0 <= k < D).
```

The pair `(P_n,D_n)` generates `M_D(F_2)`.  Indeed the cyclic Thue--Morse
word has least period `D`: any least cyclic period divides `D`, hence is
`2^a`, and `D_n(0)=0` whereas `D_n(2^a)=1`.  Thus its cyclic translates
separate every pair of coordinates.  Products of the translated diagonal
idempotents give all coordinate idempotents, and `P_n` then gives every
matrix unit.

Consequently the quotient

```text
EL_3(F_2<x,y>) -> EL_3(M_D(F_2))=SL_(3D)(F_2),
x |-> P_n,  y |-> D_n,
```

is onto.  Property `(T)` of the fixed noncommutative universal lattice
therefore makes the images of one fixed Kazhdan generating set uniform
expanders on the nonzero vectors of `F_2^(3D)`.  This verifies the proposed
mother-group idea at the level of separate finite quotients.

It does **not** give a compatible actor on the nested Leavitt prefix heads.
Write

```text
A_n=M_(2^n)(F_2),             A_n -> A_(n+1), a |-> a tensor I_2.
```

If matrices `G_n in GL_(2^n)(F_2)` give compatible inner automorphisms,

```text
Ad(G_(n+1))|(A_n tensor I_2)=Ad(G_n tensor I_2),        (AMH1)
```

then

```text
G_(n+1)=G_n tensor Q_n                               (AMH2)
```

for some `Q_n in GL_2(F_2)`.  This follows because
`(G_n^(-1) tensor I_2)G_(n+1)` centralizes
`A_n tensor I_2`, whose commutant is `I_(2^n) tensor M_2`; over `F_2`
there is no scalar ambiguity.

Hence every fixed family of compatible prefix-head normalizers acts through
tensor products of one-qubit matrices and preserves the set of decomposable
tensors.  It cannot be transitive on all nonzero prefix vectors once
`n>=2`.  In particular the odometer restrictions cannot satisfy `(AMH1)`:
`P_(n+1)` is one cycle of length `2^(n+1)`, whereas
`P_n tensor Q` has order at most `2^n` for every `Q in GL_2(F_2)` whose
permutation action is used here, and is never that single cycle.

The same obstruction appears directly in self-similar notation.  For a
finite-state tree automorphism `g`, conjugation of the prefix matrix unit
`E_(u,v)` carries the tail multiplier

```text
g|_u (g|_v)^(-1).                                      (AMH3)
```

It lands in the pure level head only when the sections `g|_u` are equal for
all words `u` at that level.  The binary odometer has different carry and
noncarry sections, so its level permutation is not an inner normalizer of
the full prefix head even though it permutes the diagonal cylinder
projections.  The automatic Thue--Morse state has the analogous unresolved
tail-state dependence.

Thus automatic `P_n,D_n` data give a genuine uniform finite-level **linear**
actor, but not the constant-relator-cost symplectic/Pauli actor required by
`kazhdan-transitive-pauli-actor-localizes-one-mixed-word`.  A successful
compiler must add a uniform state-decoupling mechanism which removes the
section multiplier `(AMH3)` on off-diagonal roots.  Merely adjoining the
odometer and its finite automaton states does not do this.

