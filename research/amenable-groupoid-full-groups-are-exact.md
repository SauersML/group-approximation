---
rg: 2
id: amenable-groupoid-full-groups-are-exact
kind: claim
title: Every topological full group of an amenable ample groupoid with compact unit space is exact (the synthesis diagnostic Q-exact)
distinct_from:
  fp-simple-nonexact-group: that asks for any finitely presented simple non-exact group; this asks whether one large host class, full groups of amenable groupoids, is exact, and its failure through V would give that group.
  thompson-group-f-is-exact: that is the exactness of Thompson's F, which this implies through V = [[Cuntz groupoid]]; this is the statement for all amenable ample groupoids.
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that shows Boone–Higman forces a non-exact finitely presented simple group; this asks whether amenable-groupoid hosts can ever be that group.
artifacts:
  - research/artifacts/gq-bh-synth-obstructions.md
---

**OPEN.** Let `𝒢` be an amenable ample Hausdorff groupoid with compact unit space. Then `[[𝒢]]` is exact, and so
are all its subgroups. This is the diagnostic Q-exact of `research/artifacts/gq-bh-synth-obstructions.md` §6. If
it holds, no amenable-groupoid host contains Osajda's decidable non-exact group
(`osajda-decidable-nonexact-group-satisfies-boone-higman`).

## It already contains the exactness of Thompson's F

- `V = [[𝒢_2]]` for the Cuntz groupoid `𝒢_2`, which is amenable. Both facts are standard (Renault; Matui and
  Nekrashevych) and are recalled here, not re-read. `F ≤ T ≤ V`.
- So this claim implies `thompson-group-f-is-exact` (route `thompson-f-exact-via-amenable-full-groups`). That is
  open: Scarparo (arXiv:2109.01111, TeX l.283, read at source) proves only "F is exact if and only if T is
  exact". A bounded search (2026-09-18) found no later resolution.
- Conversely, if `F` is not exact, then `T` and `V` are finitely presented simple non-exact groups. This claim
  fails, `fp-simple-nonexact-group` holds, and exactness is dead as a separator for Boone–Higman.

## Why the relative-amenability method stalls for V (lane computation, elementary)

Scarparo's method: find a compact `Γ`-space that is `(Γ, Λ)`-amenable with `Λ` exact, then apply Brown–Ozawa
Prop. 5.2.1, quoted at l.164 of his TeX. For `V` on the Cantor set `C` the natural choice is
`Λ = V_(0^∞) = Stab_V(0^∞)`:
- `V/Λ` is the set of sequences tail-equivalent to `0^∞`.
- `μ_n(ξ) = (1/(n+1)) Σ_(k=n)^(2n) δ_(ξ|k 0^∞)` is locally constant in `ξ`.
- An element acting on a cone by the prefix replacement `s ↦ t` shifts the index `k` by `δ = |t| − |s|`,
  once `n >= |s|`. So `‖v μ_n(ξ) − μ_n(vξ)‖_1 <= 2|δ|/(n+1) → 0` uniformly.

So `C` is `(V, V_(0^∞))`-amenable, and `V` is exact if `V_(0^∞)` is. But `V_(0^∞)` is an extension of the germ
group `Z` by the union of the rigid stabilizers of the clopen sets `C ∖ [0^k]`, each a copy of `V`. So this
reduces `V` to `V`. For `T`, point stabilizers are `F`-like and do not contain `T`, which is why Scarparo's
reduction works there. A reduction for `V` needs a compact `V`-space that is amenable relative to a subgroup not
containing `V`.

## Other test cases on main

- **Haagerup hosts.** `V`, `T`, `F` and SFT full groups (Farley), and `nV` (`brin-thompson-groups-nv-are-a-t-menable`),
  are Haagerup. By `haagerup-hosts-carry-no-weak-expander`, a non-exact subgroup of them must be a-T-menable, of
  Arzhantseva–Osajda type, and not expander-type.
- **Röver–Nekrashevych groups.** The Nekrashevych groupoid of a contracting self-similar group `G` is amenable
  (Nekrashevych; recalled, not re-read), and `V_d(G) ⊇ G`. So this claim implies that every contracting
  self-similar group is exact. A non-exact contracting group would refute it. `V_d(G)` is then finitely
  presented (Nekrashevych, cited in arXiv:2407.03149v1 l.209).

## Lesson for general BH

Q-exact is not a new question. Its first case is Thompson's `F`. A falsity route for Boone–Higman through
exactness would first have to prove `F` exact. A proof route through amenable-groupoid hosts, meanwhile, needs a
non-exact subgroup of `V`-type groups, or a non-amenable groupoid. The cheapest non-amenable option is a twisted
Brin–Thompson group of a non-exact actor (`fp-simple-nonexact-group-via-nonexact-type-a-actor`). So on the
host side the exactness diagnostic splits into two concrete questions: is `F` exact, and does some non-exact
group have a type (A) action?
