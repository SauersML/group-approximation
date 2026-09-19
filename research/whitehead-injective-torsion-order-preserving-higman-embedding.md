---
rg: 2
id: whitehead-injective-torsion-order-preserving-higman-embedding
kind: claim
title: A Whitehead-injective Higman embedding preserving every torsion order
distinct_from:
  torsion-free-higman-embedding: that preserves torsion-freeness but carries no K-theoretic control; this simultaneously preserves the full torsion-order set and injects the Whitehead group.
  whitehead-injective-torsion-free-embedding: that is only the torsion-free specialization; this theorem applies to every finitely generated recursively presented group.
  whitehead-vanishing-torsion-free: that asks for universal vanishing; this constructs embeddings and does not assert that either Whitehead group vanishes.
---

Every finitely generated recursively presented group K admits an embedding

    j : K -> H

into a finitely presented group H such that

    Wh(K) -> Wh(H)

is injective and

    Tord(H) = Tord(K).

Thus the host creates no finite torsion orders at all. The theorem is
established by [[whitehead-injective-via-waldhausen-higman-rope]].
