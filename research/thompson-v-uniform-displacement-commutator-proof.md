---
rg: 2
id: thompson-v-uniform-displacement-commutator-proof
kind: route
title: Two commutators turn any nontrivial element of V into a clopen 3-cycle conjugate to a cylinder 3-cycle
target: thompson-v-rank-models-displace-every-element-uniformly
requires:
  - thompson-v-finitely-presented-infinite-simple
---

**Rank inequality.** In any unital ring with a rank function, `[g,h] - 1 = ((g - 1) - (h g h^(-1) - 1)) h g^(-1) h^(-1)`.
Rank is conjugation invariant, so `rk(sigma([g,h]) - 1) <= 2 rk(sigma(g) - 1)`.

**Clopen 3-cycles are conjugate.** Let `w` cycle three disjoint clopens `A -> B -> C -> A` by maps
`alpha : A -> B` and `beta : B -> C`, with `w^3 = 1`, `w|_C = (beta alpha)^(-1)`, `w = 1` off `A ∪ B ∪ C`,
and `D = X \ (A ∪ B ∪ C)` nonempty. Let `t` be a cylinder 3-cycle `[a'] -> [b'] -> [c'] -> [a']` with
prefix replacements `tau_b : [a'] -> [b']` and `tau_c : [a'] -> [c']`. Choose:
- `kappa in V` carrying `A` onto `[a']`;
- any element of `V` carrying `D` onto `X \ ([a'] ∪ [b'] ∪ [c'])`.

Define `g` by:
- `g|_A = kappa`;
- `g|_B = tau_b kappa alpha^(-1)`;
- `g|_C = tau_c kappa alpha^(-1) beta^(-1)`;
- `g` on `D` equal to the second chosen element.

Then `g in V`, and a direct check on `[a'], [b'], [c']` gives `g w g^(-1) = t`.

**Two commutators.** Let `z != 1`.
1. **First commutator.** Choose a cylinder `[a]` with `z[a] ∩ [a]` empty. Passing to `[a0]` if needed,
   also `[a] ∪ z[a] != X`, because `z[a1]` misses `[a0] ∪ z[a0]`. Fix a point `x_0` outside
   `[a] ∪ z[a]`. Choose disjoint cylinders `[c], [d]` outside `[a] ∪ z[a]` that avoid `x_0` and
   `z^(-1)(x_0)`. Then `S = [a] ∪ [c] ∪ [d] ∪ z[a] ∪ z[c] ∪ z[d]` is a clopen set missing `x_0`, so
   its complement contains two disjoint cylinders. Put `u = t_(a,c,d)` and `y = [z, u]`.
   - `u` fixes `z[a]` pointwise, while `z u z^(-1)` carries `z[a]` onto the disjoint clopen `z[c]`.
   - So `y != 1`, and `supp(y) ⊆ S` is clopen and `y`-invariant.
2. **Second commutator.** Choose a cylinder `[p] ⊆ supp(y)` with `y[p] ∩ [p]` empty, and disjoint
   cylinders `[q], [r]` outside `S`. Put `v = t_(p,q,r)`. Then `[y, v]` is the clopen 3-cycle
   `[p] -> y[p] -> [q] -> [p]`, acting as `y` on `[p]`, as `v y^(-1)` on `y[p]` and as `v^(-1)` on `[q]`.
   It is the identity elsewhere: `y^(-1)[p]` misses `[p]`, `[q]` and `[r]`. Its union misses `[r]`.

By conjugacy and the rank inequality, `d_3 = rk(sigma([y,v]) - 1) <= 2 rk(sigma(y) - 1) <= 4 rk(sigma(z) - 1)`.

**Nontriviality.** If `d_3 = 0` then `sigma(t) = 1`. The normal closure of `t` is `V` by simplicity,
so `sigma` is trivial. The converse is clear. QED
