---
rg: 2
id: nilpotent-endomorphism-families-have-periodizations
kind: claim
title: Torsion-free nilpotent endomorphism families share marked periodizations
distinct_from:
  abelian-matrix-hnns-have-marked-finite-quotients: that treats finite-rank free abelian packets by direct congruence reduction; this treats arbitrary finitely generated torsion-free nilpotent packets through Hirsch rank and pro-p completion.
  full-h1-rank-free-endomorphism-families-periodize: that assumes full-rank abelianization for free-group endomorphisms; here injectivity forces full-rank abelianization because an isomorphic subgroup of a finitely generated nilpotent group has finite index.
  single-free-endomorphism-has-marked-finite-quotients: that handles one arbitrary free-group branch through mapping-torus residual finiteness; this handles finitely many simultaneous branches but uses nilpotence essentially.
---

ESTABLISHED.  Let `Gamma` be a finitely generated torsion-free nilpotent
group, let `phi_1,...,phi_r:Gamma->Gamma` be injective endomorphisms, and let
`1!=y in Gamma`.  There is one finite `p`-group quotient

```text
q:Gamma->Q,                  q(y)!=1,                  (NEP1)
```

on which every `phi_i` descends to an automorphism.

The subgroup `phi_i(Gamma)` is isomorphic to `Gamma`, hence has the same
Hirsch length.  A full-Hirsch-length subgroup of a finitely generated
nilpotent group has finite index.  Its image in `Gamma_ab` therefore has
finite index, so `phi_i` induces a full-rank map on the free part of
`Gamma_ab`.

Choose a prime `p` avoiding the torsion order of `Gamma_ab` and all the
nonzero determinants of those finitely many maps.  Finitely generated
torsion-free nilpotent groups are residually `p` for every prime.  Thus
`Gamma` embeds in its pro-`p` completion `P`, with `y` nontrivial.  Every
`phi_i` extends continuously to `P`, and acts invertibly on

```text
P/Phi(P) ~= H_1(Gamma;F_p).                            (NEP2)
```

The pro-`p` Burnside basis theorem makes the extension surjective, and a
finitely generated profinite group is Hopfian, so it is an automorphism.

Choose an open normal `U` not containing `y`, and intersect every open
subgroup of index at most `[P:U]`.  The resulting `C` is open,
characteristic, and contained in `U`.  Hence `Q=P/C` is finite, detects `y`,
and is invariant under every `phi_i`.  In particular the multiple ascending
presentation maps to the finite marked group

```text
<Gamma,t_i | t_i g t_i^(-1)=phi_i(g)>
      -> Q rtimes <bar phi_1,...,bar phi_r>.            (NEP3)
```

Thus nonabelian nilpotent packet geometry cannot supply the non-fusion
recurrence: every finite family of proper injective branches has a common
exact marked periodization.  The surviving finitely generated RF boundary
lies beyond torsion-free nilpotent packets, notably the multi-free case with
a singular-`H_1` branch and the general simultaneous linear periodic-point
problem.
