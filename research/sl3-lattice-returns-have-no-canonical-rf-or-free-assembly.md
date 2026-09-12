---
rg: 2
id: sl3-lattice-returns-have-no-canonical-rf-or-free-assembly
kind: claim
title: Higher-rank lattice returns admit neither canonical residual-orbit descent nor free assembly
invalidates:
  - sl3-return-spatialization-via-rf-or-free-assembly
artifacts:
  - research/sl3-return-assembly-firewall-proof.md
distinct_from:
  sl3-noncompact-return-cocycle-spatializes: that asks for noncanonical simultaneous implementers after one embedding into a matrix ultrapower; this rules out two exact constructions inside the amplified profinite base and does not constrain new ultrapower implementers.
  noncompact-right-holonomy-is-not-compact-profinite: that proves outer-class injectivity for the rank-one translation factor and separates lattice returns from compact translations; this proves the higher-rank version and extracts the residual-finite-orbit and property-FA assembly firewalls.
  separate-return-models-do-not-force-a-common-base: that gives abstract tensor/free/orbit-sum defects for a free family of automorphisms; this applies the actual outer classes and property (T) of the cocompact `SL_3(Q_p)` lattice.
---

Let

```text
G=SL_3(Q_p), A=SL_3(Z[1/p]),
Q=L^infinity(G) rtimes A,
alpha_g(f)(x)=f(xg)
```

with `alpha_g(u_a)=u_a`, and let the torsion-free cocompact lattice
`Lambda'<G` act by these right translations.  Then:

1. The outer action is faithful:

   ```text
   Lambda' -> Out(Q),       g |-> [alpha_g]              (RAF1)
   ```

   is injective.  It remains injective after every standard finite matrix
   amplification of `Q`.
2. Let `H` be any proper finite-index normal subgroup of `Lambda'`.  The
   canonical residual-orbit construction with blocks indexed by
   `Lambda'/H` and block `gH` labelled by the right-translate copy
   `alpha_g(Q)` cannot be made well defined, even allowing inner changes of
   coordinates and finite matrix amplification.  Indeed representative
   independence would make every `alpha_h`, `h in H`, inner, contradicting
   `(RAF1)` because `H` is infinite.
3. `Lambda'` has property (T), hence Serre's property FA.  It has no
   nontrivial free-product, amalgamated-free-product, or HNN decomposition
   from which the separately embeddable cyclic return crossed products could
   be assembled by a Bass--Serre argument.

Consequently residual finiteness supplies finite permutations of return
**labels**, but no exact identification of the corresponding base embeddings;
and the rank-one free-generator construction has no higher-rank analogue.
Neither statement refutes `sl3-noncompact-return-cocycle-spatializes`:
after a specially chosen `pi:qQq->R^omega`, a nontrivial kernel return may
become spatial even though it is outer in `Q`.  Producing that common
embedding and killing its relative-commutant multiplier remain precisely the
open conditions `(HCS3)`.

DERIVATION
sl3-return-assembly-firewall-proof
