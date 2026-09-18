---
rg: 2
id: telescope-fixed-points-are-singular-on-a-parse-shift
kind: claim
title: The self-simulation equation θ = (s on the first annulus, θ on every deeper annulus) has a unique homeomorphic solution θ_s for every seed s; θ_s is a two-state transducer when s ∈ V, fixes the parse shift of never-terminating hierarchies, is singular on all of it, and carries the whole seed group in its germs at every point of it
requires:
  - telescopic-germ-bases-in-v-germ-extensions-are-v-separated
distinct_from:
  telescopic-germ-bases-in-v-germ-extensions-are-v-separated: that shows self-simulation inside finite germ extensions of V collapses into V; this constructs the genuinely self-simulating elements and identifies their singular set, which is an uncountable subshift of finite type, not a finite set.
  deterministic-time-lifts-inherit-quantum-rigidity: that is about rigidity of time-deterministic SFT codings; this produces the group elements whose defining relations are a hierarchical parse rule, the object Conjecture G2-fp of the master route asks to be rigid.
---

**ESTABLISHED** by `telescope-fixed-points-parse-shift-proof` (lane proof, elementary, no imports.
Not reviewed; no priority claimed).

**Setup.** Let `C = {0,1}^ω`, `A_0 = 1C`, `A_n = 0^n 1 C` and `α_n(w) = 0^n 1 w`. For a homeomorphism `s`
of `C`, the **self-simulation equation** asks for a homeomorphism `θ` such that:
- `θ(1w) = 1 s(w)`: the seed acts on the first annulus;
- `θ = α_n θ α_n^{-1}` on `A_n` for every `n ≥ 1`: on every deeper annulus the solution acts by a copy of itself.

This is the fixed-point, Kleene-style form of the telescope. The host simulates itself at every
scale, with seed `s` at the top.

**Parse.** Let `U = (0^+1)^* 1`, a prefix code. Every `w ∈ C` either has a unique prefix `u ∈ U`
(its *parse terminates* at depth `|u|`), or lies in the **parse shift**
`Y = {w : w_0 = 0 and w contains no factor 11}`. `Y` is a closed, perfect, uncountable one-sided
subshift of finite type: a golden-mean shift with a first-letter constraint.

**Theorem.**
1. **Existence and uniqueness.** The equation has exactly one solution, `θ_s(uw) = u s(w)` for `u ∈ U`,
   with `θ_s` the identity on `Y`. The map `s ↦ θ_s` is an injective homomorphism
   `Homeo(C) → Homeo(C)`.
2. **Finite state.** If `s ∈ V` then `θ_s` is computed by a finite asynchronous transducer: two
   parse states, "block start" and "inside a block", followed by `s`. So for any finite
   `S ⊂ V`, `⟨V, θ_S⟩` lies in the Grigorchuk–Nekrashevych–Sushchanskii rational group.
3. **Singular set.** For `s ≠ id`, `Sing(θ_s) = Y ∪ ⋃_{u∈U} u·Sing(s)`. In particular `θ_s` is not a
   finite germ extension element: its singular set contains a Cantor set.
4. **The seed lives everywhere on Y.** For every `y ∈ Y` the germ map `s ↦ germ_y(θ_s)` is an injective
   homomorphism. The isotropy of `⟨θ_S⟩` at every point of the parse shift contains a copy of `⟨S⟩`.
5. **One chain is capped.** For finite `S ⊂ V` the elements of `⟨V, θ_S⟩` are ω-automatic bijections.
   So by `definable-parameter-hosts-cap-simple-subgroups-at-pspace` (bh-free-32) every finitely
   generated simple subgroup has word problem in PSPACE. Self-simulation along a single chain of
   annuli creates no complexity.

**Reading.** Compare with `telescopic-germ-bases-in-v-germ-extensions-are-v-separated`, item 4.
- In a finite germ extension of `V` a self-simulated copy must eventually lie in `V`, so the
  hierarchy is forced to terminate.
- The fixed point `θ_s` is what happens when it does not terminate. The singular set is exactly the
  space of never-terminating parses, and it is an SFT.
- That is the Cantor-group incarnation of a fixed-point tiling. Points of `Y` are the
  "infinite-level" points of the hierarchy, and the parse rule `U` is the cross-depth rule that
  bh-free-22's locality principle demands.

**Lesson for general BH.** Genuine self-simulation turns a finite singular set into an SFT
singular set, which is the non-terminating hierarchy, and it spreads the seed group over the
isotropy of every point of that SFT. So the natural finiteness theorem for self-simulating hosts
is not Belk–Hyde–Matucci (finite singular sets) but a theorem about full groups over an SFT: the
master route's P2′, with the parse shift as the SFT. Along a single chain the parse shift is
one-dimensional and the host is PSPACE-capped. To host hard inputs, the hierarchy must be indexed
by a one-ended group, with locally unique parse. This is exactly Conjecture G2-fp;
`self-simulating-hosts-over-one-ended-parse-shifts` records the precise statement.
