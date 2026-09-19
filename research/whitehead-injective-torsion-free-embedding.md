---
rg: 2
id: whitehead-injective-torsion-free-embedding
kind: claim
title: A Whitehead-injective torsion-free Higman embedding
distinct_from:
  torsion-free-higman-embedding: that gives an embedding of groups alone; this theorem adds injectivity on Whitehead groups.
  whitehead-injective-torsion-order-preserving-higman-embedding: that is the stronger theorem for arbitrary finitely generated recursively presented groups and preserves the exact torsion-order set; this is its torsion-free specialization.
  whitehead-vanishing-torsion-free: that is the universal vanishing conjecture; this is an embedding theorem and does not assert vanishing.
  whitehead-vanishing-finitely-presented-torsion-free: that is the remaining vanishing statement for the target class; together with this theorem it implies the recursively presented and global torsion-free cases.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Every finitely generated recursively presented torsion-free group K admits an
embedding K->H into a finitely presented torsion-free group such that

    Wh(K) -> Wh(H)

is injective.

**ESTABLISHED 2026-08-30.** The route
[[whitehead-injective-torsion-free-via-torsion-orders]] specializes the
stronger torsion-order-preserving theorem
[[whitehead-injective-torsion-order-preserving-higman-embedding]].

The construction is Higman's rope with edge group L=F*_R F. Waldhausen's
class-Cl theorem makes Wh_Z(L) contractible, and the unconditional general
HNN fibration has a constant Nil-to-vertex arrow. Therefore the vertex map
is Whitehead-injective. Chiodo supplies the finitely presented torsion-free
host needed by the rope, and Bass--Serre theory preserves torsion-freeness.

This closes the previously missing transfer step in the finitely-presented
route. It does not by itself prove Whitehead vanishing: that route still
requires [[whitehead-vanishing-finitely-presented-torsion-free]].
