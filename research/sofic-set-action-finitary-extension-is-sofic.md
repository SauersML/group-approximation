---
rg: 2
id: sofic-set-action-finitary-extension-is-sofic
kind: claim
title: A sofic set action has a sofic finitary-symmetric extension
distinct_from:
  gkp-wreath-permanence-theorem: that treats restricted direct-sum lamp groups; the finitary symmetric kernel is not a restricted direct sum and is not residually finite, so it requires a separate fibrewise chart argument
  finitary-extension-ce-iff-action-lifts-to-normalizer: that characterizes Connes embeddability of the resulting crossed product by a normalizer lift; this supplies Connes embeddability from a sofic set action
  single-lamps-recover-set-action: that recovers a set action from automorphism charts on an abelian lamp group; this constructs group microstates for the nonabelian finitary-symmetric extension
---

Let a countable sofic group `H` act soficly on a countable set `Y`.  Then

```text
Sigma(Y,H) = Sym_fin(Y) rtimes H
```

is sofic.  Consequently `L(Sigma(Y,H))` is Connes embeddable.

The point is that a GKP orbit approximation supplies, over almost every actor
state, an injective labelled copy of every finite support that occurs in a
test window.  Transporting the retained finitary permutations through those
labels gives a fibre permutation.  The orbit covariance equation is exactly
the conjugation equation needed for the semidirect product.  Cartesian-power
amplification turns the positive separation supplied by one moved label into
the usual asymptotically free sofic separation.

This statement is not amenable-by-sofic permanence.  It uses soficity of the
specific action, and therefore does not apply to the full Kun--Thom action,
which is nonsofic.

DERIVATION
sofic-set-action-finitary-extension-proof
