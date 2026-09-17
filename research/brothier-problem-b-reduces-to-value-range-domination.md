---
rg: 2
id: brothier-problem-b-reduces-to-value-range-domination
kind: claim
title: "For residually finite Γ, C(C,Γ) ⋊ V is a-T-menable iff some cnd function confines the values of low-energy maps to a finite subset of Γ"
distinct_from:
  cantor-integer-maps-by-v-have-haagerup-property: that is the open case Γ = Z of Brothier's Problem B; this proves, for every residually finite Γ, that the positional half of properness (supports, depths, clopen patterns) is automatic through congruence quotients and Farley's theorem, so Problem B is equivalent to a pure value-range condition, which stays open.
  cantor-integer-maps-sup-norm-is-cnd-dominated: that is the open value-range condition for Γ = Z; this is the equivalence that makes it sufficient.
  twisted-power-cloning-groups-embed-in-v: that embeds C(C,Q) ⋊ V in V for finite Q; this applies that embedding to every congruence quotient of C(C,Γ) ⋊ V at once and glues the pulled-back Farley functions with summable weights.
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

**ESTABLISHED** by `brothier-problem-b-value-range-domination-proof` (unreviewed by a
verifier lane as of 2026-09-17).

## Setting

- `C = {0,1}^N`, `V` Thompson's group acting on `C`.
- `Γ` a countable group, `A_Γ = C(C,Γ)` the locally constant maps with pointwise
  product, `V` acting by `(h·f)(x) = f(h^{-1}x)`, and
  `G_Γ = A_Γ ⋊ V` with `(f,h)(f',h') = (f·(h·f'), hh')` (Brothier's Problem B group).
- For `f ∈ A_Γ` write `ran(f) = f(C) ⊆ Γ`, a finite set.

## Statement

Convention: a cnd function `ψ` satisfies `ψ(e) = 0` and `ψ(g^{-1}) = ψ(g)`.

Let `Γ` be residually finite. The following are equivalent.

1. `G_Γ` has the Haagerup property.
2. **(Value-range domination.)** There is a conditionally negative definite
   function `ψ` on `G_Γ` such that for every `R`, the set
   `⋃ { ran(f) : f ∈ A_Γ, ψ(f) ≤ R }` is a finite subset of `Γ`.

For `Γ = Z`, condition 2 says: some cnd `ψ` on `C(C,Z) ⋊ V` satisfies
`ψ(f) ≥ F(‖f‖_∞)` on `A` for some `F: N → R` with `F → ∞`.

## What this changes

- Properness on `A_Γ` has two parts: bounding the values of `f`, and bounding the
  clopen pattern of `f` (depth, number of pieces, position). The second part was the
  source of the codimension-one failures recorded on
  `cantor-integer-maps-by-v-have-haagerup-property` and on
  `brin-thompson-groups-nv-are-a-t-menable`. This claim shows the second part is
  free: it is supplied by Farley's cube complex on the finite congruence quotients.
- What remains is a coarse, magnitude-only statement. Its negation says that every
  cnd function is bounded on some set of maps whose values leave every finite subset
  of `Γ` (the set may depend on the function). A sufficient witness is one such set on
  which all cnd functions are bounded, i.e. a value-unbounded subset of `A_Γ` with
  relative property (T) in `G_Γ`. For `Γ = Z`, a failure of condition 2
  refutes Problem B for `Z` and, through `C(C,Z) ⋊ V ≤ 2V`
  (`cantor-maps-by-v-embed-in-next-brin-thompson-group`), proves
  `brin-thompson-2v-is-not-a-t-menable`.

## Imports

- `twisted-power-cloning-groups-embed-in-v` with `φ0 = φ1 = id`, identified with
  `C(C,Q) ⋊ V` for finite `Q` in the artifact, Section 2, Remark (finite Γ).
- `thompson-v-has-haagerup-property` (Farley).
- Standard facts on cnd functions: pullbacks along homomorphisms, nonnegative
  combinations and pointwise limits are cnd; `√ψ` is subadditive when `ψ(g) = ‖b(g)‖²`
  for a cocycle `b` (Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Ch. 2 and
  App. C; textbook facts, cited by chapter and not imported verbatim).
