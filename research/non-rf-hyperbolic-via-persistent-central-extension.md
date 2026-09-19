---
rg: 2
id: non-rf-hyperbolic-via-persistent-central-extension
kind: route
title: A persistent finite cohomology class gives a hyperbolic non-residually-finite extension
target: non-residually-finite-hyperbolic-group
requires:
  - persistent-degree-two-class-on-hyperbolic-group
  - finite-central-extension-rf-iff-virtually-splits
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Take `H` residually finite hyperbolic, `p` prime, and `0 ≠ α ∈ H^2(H; C_p)`
persistent — nonzero on every finite-index subgroup.  Form the central
extension

```text
1 -> C_p -> E_α -> H -> 1.
```

By `finite-central-extension-rf-iff-virtually-splits`, `E_α` is residually
finite if and only if `α` dies on some finite-index subgroup, which
persistence forbids.  So `E_α` is not residually finite.  And `E_α` is
hyperbolic: it is a finite extension of a hyperbolic group, hence
quasi-isometric to it.

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
