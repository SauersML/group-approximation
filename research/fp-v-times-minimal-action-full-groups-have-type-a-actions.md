---
rg: 2
id: fp-v-times-minimal-action-full-groups-have-type-a-actions
kind: claim
title: If the topological full group of G_V times a minimal action groupoid is finitely presented, its clopen action is of type (A)
distinct_from:
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is the open finiteness premise asserting finite presentation of A(G_V × (Λ ⋉ X)); this assumes finite presentation and derives a type (A) action, so it is the consumer of that premise, not a case of it.
  fp-full-binary-cantor-groups-have-type-a-actions: that needs the standard binary V inside the full group; this works on the unit space C × X directly and needs no identification of C × X with binary Cantor space.
  v-times-ample-full-groups-are-generated-by-transpositions: that proves F = S = A for G_V times any ample groupoid and says nothing about actions on clopen sets; this derives a type (A) clopen action from finite presentation and minimality.
---

**ESTABLISHED** by `fp-v-times-minimal-action-full-groups-type-a-proof`. Not
independently reviewed.

## Statement

Let `Λ` act minimally by homeomorphisms on a nonempty compact metrizable totally
disconnected space `X`. Put `T = G_V × (Λ ⋉ X)` on `Y = C × X`, and let `F(T)` be
the topological full group: the homeomorphisms of `Y` induced by compact open
bisections `B ⊆ T` with `s(B) = r(B) = Y`. If `F(T)` is finitely presented, then
the action of `F(T)` on the proper nonempty clopen subsets of `Y` is of type (A).
Hence every subgroup of `F(T)` lies in the permutational class `B_A`, has solvable
word problem, and embeds in a finitely presented simple group.

When `Λ` is also finitely presented and `X` is a minimal free subshift of finite
type, `F(T) = A(T)` by `v-times-ample-full-groups-are-generated-by-transpositions`.
So premise (P2) of `boone-higman-via-v-times-aperiodic-sft-full-groups` gives
the hypothesis.
