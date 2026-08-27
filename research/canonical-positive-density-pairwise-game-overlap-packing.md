---
rg: 2
id: canonical-positive-density-pairwise-game-overlap-packing
kind: claim
title: Compile one finite-game gap into a static packing of one canonical positive-density head
distinct_from:
  canonical-positive-density-hs-power-overlap-return: That must control repeated returns of one word and hence all cycle powers; this allows unrelated translating words and asks only for their pairwise relative corners.
  source-specific-pointed-rank-router-face: That compiles arbitrary independent-set overlap loss through a pointed affine block router; this uses the already strict cyclic acceptance compressor and asks for a common selected Hecke corner.
  block-encoded-acceptance-still-needs-corner-return: That isolates one selected mixed corner moment; this asks for a finite cycle-compatible family of such moments sharing one authenticated source.
---

Fix a Culf--Mastel game, its block-encoded cyclic acceptance contraction, and
its finite-matrix soundness constant `rho<1`.  Starting from one rational
finite-packet idempotent `q` with fixed canonical trace `tau(q)=alpha>0`, and
for any prescribed fixed integers `M,L`, construct effectively an ordinary
group extension and unitary group words `v_0,...,v_(M-1)` such that:

1. adjoining the words and their controller relations does not change
   `tau(q)=alpha`; in particular `alpha` is independent of `M,L`;
2. every canonical-profile normalized-HS microstate, after fixed-packet
   exactification, satisfies

   ```text
   ||q v_i^* v_j q||_2^2
      <=(alpha+o(1))rho^(2L)+o(1)       whenever i!=j;              (PGO1)
   ```

3. on a perfect instance, one exact possibly properly infinite
   representation extends with `q!=0` and all the perfect selected corners.

The same packet head must be used for every pair.  Giving each edge an
independent packet atom whose joint trace decays with `M` does not satisfy the
claim.

## Attempts

- Taking `v_i=u^(iL)` reduces to
  `canonical-positive-density-hs-power-overlap-return` and imports the
  unwanted no-return problem.
- Independent fresh controller packets make the joint selected head
  exponentially small in the number of pairs, so packing capacity never
  becomes supercritical.
- Reusing one controller packet preserves `alpha` and is the live static
  approach.  The remaining obstruction is triangle consistency: the relative
  words necessarily satisfy
  `(v_i^*v_j)(v_j^*v_k)=v_i^*v_k`, while separately chosen block encoders do
  not.  The compiler must enforce only the selected corner moments, not global
  equality with independently chosen acceptance words.
- `pairwise-game-packing-from-corner-actuator` removes the triangle issue by
  attaching a selected-corner actuator directly to the already consistent
  ratio `v_i^*v_j`.  Under that reduction the unique remaining theorem is
  `canonical-positive-density-amplified-acceptance-corner-actuator`: amplify
  one acceptance return without diluting `q` and without imposing a global
  block-encoder equality.
- A universal local routing gadget is not enough: the tensor-closure
  obstruction recorded at `source-specific-pointed-rank-router-face` applies
  unless the relations select the canonical game moment face.  Exact
  completeness is required only for the distinguished perfect model, not for
  every locally admissible zero-loss tuple.
