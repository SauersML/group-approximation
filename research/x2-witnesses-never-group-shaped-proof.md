---
rg: 2
id: x2-witnesses-never-group-shaped-proof
kind: route
title: Injective GNS closures exclude every nonamenable group pattern, and amenable patterns are exact with UCT
target: x2-witnesses-are-never-group-shaped
requires:
  - stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses
  - nonamenable-reduced-group-algebras-avoid-hyperfinite-gns
  - amenable-action-invariant-trace-forces-amenability
---

The witness has GNS von Neumann algebra `R`, injective.

(1) If `A ≅ C*_r(G)` trace-compatibly with the canonical trace: for
nonamenable `G` the first required exclusion theorem forbids the
injective GNS closure; for amenable `G`, `A` is nuclear and satisfies
the UCT (Tu / amenable groups are a-T-menable-bootstrap), contradicting
the witness's "not both exact and UCT" clause.

(2) If `A ≅ C(X) ⋊_r G` with an invariant-measure trace of an
amenable action: the second exclusion theorem forces `G` amenable
(the invariant measure gives an invariant trace on the nuclear
`C(X)`... precisely, the crossed product's trace restricts to a
`G`-invariant trace on `C(X)`, and the theorem applies to the nuclear
coefficient algebra), so the crossed product is nuclear and satisfies
the UCT (Tu's theorem for amenable groupoids), again contradicting
the exactness/UCT clause.

(3) If unitaries `u_1, …, u_k ∈ A` generate a group `Γ ≤ U(A)` with
`τ(w) = δ_{w,e}` for all `w ∈ Γ`: the weak closure of the linear span
of `Γ` inside the GNS closure `R` is a von Neumann algebra with
faithful normal trace restricting to the canonical group trace, hence
isomorphic to `L(Γ)`; every von Neumann subalgebra of the finite
injective `R` is injective, so `L(Γ)` is injective and Connes' theorem
makes `Γ` amenable.  A nonamenable such `Γ` is impossible.
