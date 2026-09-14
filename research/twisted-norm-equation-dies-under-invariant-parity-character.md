---
rg: 2
id: twisted-norm-equation-dies-under-invariant-parity-character
kind: claim
title: An h-invariant Z/2-valued homomorphism on the units of D(N) that is nontrivial on h^2 forces Strong Atiyah for the index-2 overgroup
distinct_from:
  index-two-strong-atiyah-is-a-twisted-norm-equation: that is the norm-equation criterion itself; this is one invariant that excludes every solution of it at once.
  level15-lattice-has-invariant-parity-character-detecting-h2: that is a character on the group N for one lattice; this needs a character on the units of the division ring D(N), for any index-2 extension.
---

**ESTABLISHED** by [[twisted-norm-parity-character-proof]]. Elementary. Not
independently reviewed. No novelty is claimed.

Let `K <= C` be a subfield, `G` a torsion-free group, and `N <= G` a subgroup of
index 2 satisfying the Strong Atiyah conjecture over `K`. Fix `h` in `G` minus `N`, and
let `sigma(x) = h x h^-1` on the division closure `D_K(N)`.

Suppose `theta : D_K(N)^x -> Z/2` is a group homomorphism with `theta o sigma = theta`
and `theta(h^2) = 1`. Then `G` satisfies Strong Atiyah over `K`.
