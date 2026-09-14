---
rg: 2
id: automorphism-immersion-representatives-finite-order-proof
kind: route
title: Immersions inducing automorphisms are graph automorphisms
target: automorphism-immersion-representatives-have-finite-order
requires: []
---

Standard facts used, not re-read at source: reduced edge paths in a graph are the
unique reduced representatives of their homotopy classes rel endpoints; an
immersion maps reduced paths to reduced paths and has unique path lifting from a
given starting vertex; hyperbolic groups contain no `Z^2`.

**Step 1: surjectivity at every basepoint.** Fix `v` and a path `beta` from `v` to
`x`. For a loop `l` at `v`, `f_*[beta^{-1} l beta] = f(beta)^{-1} f_*[l] f(beta)`.
So `f_*: pi_1(R,x) -> pi_1(R,f(x))` is surjective whenever it is at `v`, which holds
because `phi` is an automorphism.

**Step 2: `f` is injective on vertices.** Suppose `f(x) = f(y)` with `x != y`. Let
`gamma` be a reduced path from `x` to `y`. Then `f(gamma)` is a reduced nonempty
closed path at `f(x)`. By Step 1 there is a loop at `x`, which we may take reduced,
call it `delta`, with `f_*[delta] = [f(gamma)]`. Both `f(delta)` and `f(gamma)` are
reduced and homotopic rel endpoints, so they are equal paths. Unique path lifting
from `x` gives `delta = gamma`, so `gamma` is closed and `x = y`, a contradiction.

**Step 3: `f` is injective on edges.** Two distinct edges with the same image edge
start at vertices with the same image, hence at the same vertex by Step 2. That
contradicts local injectivity at that vertex. So `f` is injective on the edges of
the subdivided domain.

**Step 4: `f` is surjective.** Let `e` be an edge of `R`.
- **A loop through `e`.** Walk forward from the end of `e`, and backward from the
  start of `e`, never backtracking; this is possible because every vertex has
  valence at least two. Each walk eventually closes up a cycle, giving reduced
  paths `P_1` and `P_2` leading to cycles `C_1` and `C_2`. The closed path
  `e P_1 C_1 P_1^{-1} e^{-1} P_2 C_2 P_2^{-1}` is reduced and passes through `e`.
  This is standard.
- **Moving it to `f(v)`.** Conjugate it by a reduced path from `f(v)` and reduce.
  The result is a reduced closed path at `f(v)` through `e` or `e^{-1}`, since
  cancellation can only remove the conjugating path.
- **Lifting it.** By Step 1 this class is `f_*[delta]` for a loop `delta` at `v`,
  which we may take reduced. Then `f(delta)` is reduced and homotopic to the
  reduced path, so equal to it. Hence `e` lies in `f(R)`.

**Step 5: `f` is a combinatorial automorphism.** By Steps 2--4, `f` is a bijection
from the edges of the subdivided domain onto the edges of `R`. Subdividing only
increases the number of edges, so no edge was subdivided, and `f` is a
combinatorial automorphism of `R`.

**Step 6: finite order.** `Aut(R)` is finite, so `f^k = id` for some `k >= 1`. Then
`phi^k` is induced by the identity map composed with a change of basepoint, i.e. by
an inner automorphism `x -> g x g^{-1}`.

**Step 7: the mapping torus.** In `G = F x|_phi Z = <F, t | t x t^{-1} = phi(x)>`,
the subgroup `<F, t^k>` has index `k`. There `t^k x t^{-k} = g x g^{-1}`, so
`z = g^{-1} t^k` commutes with `F`, and with `t^k` because `t^k g t^{-k} = g`. Also
`z` has infinite order, since its image in `Z` is `k`. Hence `<F, t^k> = F x <z>`
is `F x Z`. For `F != 1` it contains `Z^2`, so `G` is not hyperbolic.
