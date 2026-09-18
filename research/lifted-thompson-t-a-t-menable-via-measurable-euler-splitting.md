---
rg: 2
id: lifted-thompson-t-a-t-menable-via-measurable-euler-splitting
kind: route
title: "A measurable splitting of the Euler extension over an almost invariant T-space, with Farley's theorem for T, gives Haagerup for T-bar"
target: lifted-thompson-t-is-a-t-menable
requires:
  - central-extension-haagerup-from-measurable-euler-splitting
  - thompson-t-euler-class-splits-over-almost-invariant-space
  - thompson-v-has-haagerup-property
---

Apply `central-extension-haagerup-from-measurable-euler-splitting` to:
- `G = T̄`, `z(x) = x + 1`, `Q = T`;
- `Q` Haagerup by `thompson-v-has-haagerup-property`, restricted to `T ≤ V`;
- the space and cocycle supplied by `thompson-t-euler-class-splits-over-almost-invariant-space`.

**Sharper entry point.** `thompson-t-co-amenable-subgroup-kills-real-euler-class` implies the
second prerequisite, with `X = T/H`. The single test case `H = PSL_2(Z)` asks whether
`PSL_2(Z)` is co-amenable in `T`.

**What cannot work.** By `perfect-extension-splittings-are-not-uniformly-integrable`, the
following cannot supply the second prerequisite:
- any space with a measurable equivariant map to `S^1`;
- any uniformly integrable splitting (in particular a bounded one, or an `L¹` one over a pmp
  space).
