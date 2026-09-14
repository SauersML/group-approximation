---
rg: 2
id: crossed-product-group-embeds-in-projective-elementary-group
kind: claim
title: Whitehead's lemma embeds abelian unit groups, and derived subgroups of unit groups, in EL_N modulo its centre
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
  - research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part2.md
---

**OPEN as a node (demoted 2026-09-13 by lane sk-subgroups; its only route is invalidated).**

The earlier statement was: for every injective homomorphism `θ : Γ -> R^×` and `N >= 2`,
`ι(g) = diag(θ(g), θ(g)^(-1), 1_(N-2))` is an injective homomorphism `Γ -> EL_N(R)`.
It is FALSE for nonabelian `Γ`:
- `ι(g)ι(h)` has `θ(g)^(-1)θ(h)^(-1)` in its second slot;
- `ι(gh)` has `θ(h)^(-1)θ(g)^(-1)` there (`whitehead-diagonal-map-is-not-multiplicative`).

**Restated claim.** Let `R` be a unital ring and `θ : Γ -> R^×` an injective homomorphism.
- (a) If `Γ` is abelian, `ι` is an injective homomorphism `Γ -> EL_N(R)` for `N >= 2`.
- (b) For every `Γ`, `δ(g) = diag(θ(g), 1_(N-1))` is an injective homomorphism `Γ -> GL_N(R)`, and for `N >= 2`,
  `δ([Γ,Γ]) ⊆ EL_N(R)`, because `diag(aba^(-1)b^(-1), 1) = diag(a,a^(-1)) · diag(b,b^(-1)) · diag((ba)^(-1), ba)`.
- (c) For `N >= 3`, the images in (a) and (b) meet `Z(EL_N(R))` trivially: conjugating `e_13(1)` by `diag(v, v^(-1), 1)`
  or by `diag(v, 1, 1)` gives `e_13(v)`.

**Instances.**
- The note's `diag(u^n, u^(-n), 1)` over `LC(X,k) ⋊ Z` is case (a).
- The derived topological full group `[[T]]'` embeds in `EL_3(LC(X,F_2) ⋊ Z)` by case (b). Lane sk-subgroups also embeds all of
  `[[T]]` over `F_2` through `diag(w_g, u^(-I(g)), 1)` (artifact part 1, Theorem B).

**Consequences that survive.**
- LEF, soficity, linear soficity and hyperlinearity pass to subgroups. So (a) and (b) transfer failures of abelian unit
  groups and of derived subgroups.
- Non-LEF of a unit subgroup reaches `EL_N(R)`, `N >= 4`, over a countable simple `R` through the ring:
  `lef-elementary-groups-force-lef-rings`, `simple-lef-rings-are-exactly-matricial`,
  `exactly-matricial-rings-have-lef-general-linear-groups`.

## Attempts
- **Route `crossed-product-group-projective-elementary-embedding-proof` (dead).** Its step 2, "ι is a homomorphism", fails
  for nonabelian `Γ`, and `whitehead-diagonal-map-is-not-multiplicative` invalidates it. The review
  (`research/artifacts/un-review3-2026-09-13-part3.md` §7) checked Whitehead's identity and the centre, not multiplicativity.
- **A direct proof of (a)–(c)** is the two identities above (artifact part 2 §4). It is not landed as a route yet. The
  firewall also invalidates the consumer routes that used the false statement, so a route here would not re-fire them.
- **Open.** A homomorphic embedding of a nonabelian `Γ` in `EL_N(R)` needs `K_1`-type information:
  - a homomorphism `ψ : Γ -> R^×` with `ψ(s) = θ(s)^(-1)` on a generating set (e.g. `ψ = θ∘α` for an automorphism `α`
    inverting it) gives `diag(θ, ψ, 1)`;
  - for Cantor minimal `Z`-systems over `F_2`, the index map supplies `ψ = u^(-I)` on the topological full group.
