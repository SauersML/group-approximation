---
rg: 2
id: non-rf-hyperbolic-via-persistent-central-extension
kind: route
title: A persistent finite cohomology class gives a hyperbolic non-residually-finite extension
target: non-residually-finite-hyperbolic-group
requires:
  - persistent-degree-two-class-on-hyperbolic-group
  - finite-hyperbolic-residual-iff-persistent-class
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

Take `H` residually finite hyperbolic, `p` prime, and `0 ≠ α ∈ H^2(H; C_p)`
persistent — nonzero on every finite-index subgroup.  Form the central
extension

```text
1 -> C_p -> E_α -> H -> 1.
```

The direction (4) implies (3) of
`finite-hyperbolic-residual-iff-persistent-class` gives the stronger
conclusion `R(E_α)=C_p`: the virtual-splitting criterion makes the
residual nontrivial, and residual finiteness of `H` bounds it by the
prime central kernel. Thus `E_α` is not residually finite. It is
hyperbolic because its finite-kernel map to `H` is a quasi-isometry.

The reverse direction of that equivalence shows the exact scope of this
route: every hyperbolic group with finite nontrivial residual gives a
persistent prime class after passing to finite index and quotienting a
finite central subgroup. The equivalence is established, while the
existence input remains open.

That is the whole route; its content is entirely in the input claim.

**Why it is worth carrying anyway.**  It converts the problem into a question
with a different shape — no geometry, no construction, one cohomology class
and a subgroup lattice — and it comes with a sharp filter attached: a
persistent class must avoid the image of `H^2_cont(H_hat; C_p)`.  A candidate
`(H, α)` can therefore be refuted quickly, which is more than can be said for
the other three live routes.  It is also the route with a genuine precedent:
in higher rank Deligne's central extension of `Sp_4(ℤ)` is exactly such a
persistent class, so the mechanism is known to occur — just not yet in a
hyperbolic group.
