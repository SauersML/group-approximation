---
rg: 2
id: leavitt-rank-models-have-uniform-root-displacement
kind: claim
title: In a characteristic-two rank model of EL_3 over the binary Leavitt algebra, root displacement is Weyl and unit invariant, at most 1/2, uniform on nonzero coefficients, and simultaneously conjugate on orthogonal idempotent tuples
distinct_from:
  binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale: that controls corona rank scales of root elements in operator-norm MF models through normal-generation counts; this gives exact rank inequalities and tuple conjugacy for homomorphisms into characteristic-two rank ultraproducts.
artifacts:
  - research/artifacts/root-displacement-rank-extraction-2026-09-12.md
---

Let `R = L_(F_2)(1,2)`, `M` a rank ultraproduct over a field of characteristic two, and
`sigma : EL_3(R) -> M^x` a homomorphism. Put `rho(a) = rk(sigma(x_12(a)) - 1)` and `rho = rho(1)`.

1. `rk(sigma(x_ij(a)) - 1) = rho(a)` for all `i != j`, and `rho(u a v) = rho(a)` for units `u, v`.
2. `rho(a) <= 1/2`, `rho(a + b) <= rho(a) + rho(b)`, and `rho(ab) <= 2 min(rho(a), rho(b))`.
3. `rho/4 <= rho(a) <= 2 rho` for every nonzero `a` in `R`.
4. For any two tuples `(e_i)`, `(f_i)` of pairwise orthogonal nonzero idempotents of the same
   length, some `g` in `EL_3(R)` conjugates every `x_12(e_i)` to `x_12(f_i)`. In particular
   `rho(e) = rho` for every nonzero idempotent `e`.

So `sigma` is nontrivial exactly when `rho > 0`, and then every nontrivial root element is
displaced by at least `rho/4`. Constancy `rho(a) = rho` on the nonzero elements of the locally
matricial subalgebra is Proposition 12 of `el3-rank-ring-rigidity-2026-09-12.md`. Parts 1–4 add
the bounds off that subalgebra, arbitrary units, and simultaneous tuple conjugacy. Proof: Section 1 of the artifact, from the exact Steinberg
relations, monomial pure infiniteness, and freeness of nonzero finitely generated projectives.
