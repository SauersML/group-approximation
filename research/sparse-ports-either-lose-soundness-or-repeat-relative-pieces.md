---
rg: 2
id: sparse-ports-either-lose-soundness-or-repeat-relative-pieces
kind: claim
title: Sparse ports either lose expander soundness or repeat bounded relative pieces
distinct_from:
  finite-offset-pauli-rectangles-violate-relative-gr-sixth: that treats the original all-port clouds; this audits the natural evasion which inserts many equality-only dummy vertices to make port-to-port peripheral elements long.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that uses every cloud vertex as a test occurrence; this shows why its unweighted Poincare proof does not survive vanishing-density ports.
---

Fix maximum degree `Delta`, normalized spectral gap `lambda>0`, and finite
equality and pair offset sets `D,P`.  In an unweighted equality-expander
cloud let `Q` be the pair-test ports and put

```text
alpha = |Q|/|V|.
```

There is a dichotomy.

1. If `alpha->0`, the standard expander-cloud decoder has no uniform
   soundness modulus on the ports.  Poincare gives only

   ```text
   Avg_{q in Q} ||A_q-bar A||_2^2
      <= (C/(lambda alpha)) Avg_{uv in E}||A_u-A_v||_2^2.       (SP1)
   ```

   This loss is real: change all port operators while leaving dummy
   operators fixed.  Only `O(Delta|Q|)` equality edges see the change, so
   normalized equality energy is `O(alpha)` while port drift is constant.

2. If `alpha>=alpha_0>0`, fixed-gap bounded-degree expansion gives a radius
   `R=R(Delta,lambda,alpha_0)` such that two distinct ports are at distance
   at most `R`.  Their peripheral difference is represented by one of the
   finitely many `D`-words of length at most `R`.  Across an unbounded family,
   some adjacent pair/peripheral relative pattern `p h` repeats at two
   essentially distinct locations.  In a complete Pauli table those two
   ports lie on mixed rectangles, so the repeated two-syllable pattern is
   exactly the relative-piece obstruction of
   `finite-offset-pauli-rectangles-violate-relative-gr-sixth`.

Hence adding unweighted equality-only dummy vertices does not repair the
relative `Gr'(1/6)` route.  A surviving sparse-port construction needs a new
**port-weighted** agreement theorem whose spectral gap and HS modulus remain
uniform despite vanishing counting density.

Pairwise equality weights alone do not supply that escape.
`weighted-equality-gap-forbids-separated-port-mass` shows that separating two
positive portions of the port measure by distance `R` forces weighted gap
`O(R^-2)`.  The remaining possibility is a higher-arity code/linearity test
whose soundness is not the Poincare inequality of one equality graph.
