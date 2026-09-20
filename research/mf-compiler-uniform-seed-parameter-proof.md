---
rg: 2
id: mf-compiler-uniform-seed-parameter-proof
kind: route
title: Retain the finite seed parameter through the Mikhailova compiler
target: mf-compiler-is-uniform-in-finite-seeds
requires:
  - arbitrary-forbidden-seed-hereditary-property-switch
  - mikhailova-fiber-product-gives-regular-mf-benign-compiler
  - mf-safe-asymmetric-hnn-replacement
artifacts:
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
  - research/artifacts/liu-new-frontiers-2026-09-20.md
  - research/artifacts/fp-inf-fin-compiler-uniform-seed-map-firewall-2026-08-26.md
---

The first premise gives a jointly computable recursive switch S(d,e),
trivial on INF and isomorphic to Carrier(d) on FIN. The latter isomorphism
uses a tail stage after the last event; no such stage is computably
selected on all inputs. Apply the existing
three-generator bridge, retaining d in its recursive kernel N_(d,e).
Augmentation onto B3(1) gives N_(d,e)<=N_+, with equality on INF; the
bridge contains the seed on FIN.

The second premise applies to every uniformly recursively enumerable
normal-subgroup family, including this jointly indexed one. Its actual
Higman host and benign witness retain d, while the ambient remains a
finite product of free groups. The fixed graph-witness product preserves
the cut N_(d,e), since this is contained in N_+.

The third premise is the special rope-HNN replacement used by
mf-safe-finite-presentation-compiler-via-mikhailova. The benign cut and
Britton normal form preserve the bridge, hence the seed on FIN. On INF,
B3(1), the graph factor and the same finite CEP/tensor-synchronization
proof supply a regular operator-MF realization of the actual rope,
regardless of its Higman host. The output presentations and words for
the finitely generated BRIDGE/Higman construction are computed jointly
in d,e. The negative seed embedding is only an existence assertion on
FIN: first choose its last-event cutoff, embed that tail copy into the
recursive switch, then compose with the bridge and rope embeddings.
There is no globally computable tuple of seed-generator images defining
a seed homomorphism on every input. This is precisely the boundary in
the uniform-seed-map firewall artifact. The argument reuses the
construction's existing proof;
it does not identify outputs for different presentations of the trivial
switch group.
