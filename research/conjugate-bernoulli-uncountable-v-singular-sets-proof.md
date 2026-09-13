---
rg: 2
id: conjugate-bernoulli-uncountable-v-singular-sets-proof
kind: route
title: Fixed sets of V are a clopen set plus finitely many points, while Bernoulli fixed sets are uncountable with empty interior
target: conjugate-bernoulli-elements-have-uncountable-v-singular-sets
requires: []
---

**Step 1: fixed sets in V.** An element `v` of `V` has a finite partition of `C`
into cones `w_i C` with `v(w_i y) = w'_i y`. On `w_i C`:
- if `w_i = w'_i`, the whole cone is fixed;
- if `|w_i| = |w'_i|` and `w_i != w'_i`, no point is fixed;
- if `|w'_i| < |w_i|`, then `w'_i y = w_i y` forces `w_i = w'_i u` with `u`
  nonempty and `y = u y`, so `y = u^infinity` and at most one point is fixed;
- the case `|w'_i| > |w_i|` is symmetric.

So `Fix(v) = K ∪ E`, with `K` clopen and `E` finite.

**Step 2: Bernoulli fixed sets.** Let `g != 1` with `<g>` of infinite index.
- `beta_g x = x` means `x(k) = x(g^(-1) k)` for all `k`, that is, `x` is constant
  on every right coset `<g> k`.
- **Uncountable.** There are infinitely many such cosets, and prescribing
  values coset by coset embeds `{0,1}^N` into `Fix(beta_g)`.
- **Empty interior.** A basic open set prescribes `x` on a finite set `F`. Some
  coset `<g> k` misses `F`, and it has at least two elements because `g != 1`.
  Giving two of them different values yields a point of the basic set outside
  `Fix(beta_g)`.

**Step 3: transfer.** Put `f = h beta_g h^(-1)` and `Phi = Fix(f) = h(Fix(beta_g))`.
Since `h` is a homeomorphism, `Phi` is closed and uncountable with empty interior.
- Let `p` in `Phi` be a point that is not V-singular. Choose an open `U` containing
  `p` and `v` in `V` with `f|U = v|U`, so that `Phi ∩ U = Fix(v) ∩ U = (K ∩ U) ∪ (E ∩ U)`.
- `K ∩ U` is open and contained in `Phi`, so it is empty. So `Phi ∩ U` is finite,
  and `p` is an isolated point of `Phi`.
- A subset of the second countable space `C` has countably many isolated points.
  So all but countably many points of `Phi` are V-singular for `f`.

**Consequence.** If `[Gamma : <g>]` is finite then `Gamma` is virtually cyclic.
So when `Gamma` is not virtually cyclic, Step 3 applies to every `g != 1`.
