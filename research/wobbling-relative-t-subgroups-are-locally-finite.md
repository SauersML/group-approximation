---
rg: 2
id: wobbling-relative-t-subgroups-are-locally-finite
kind: claim
title: "In any countable subgroup of the wobbling group of Z, and so in any subgroup of the full-shift topological full group, every subgroup with relative property (T), normal or not, is locally finite"
distinct_from:
  wobbling-normal-relative-t-subgroups-are-locally-finite: that needs H normal in Γ (it only conjectures the non-normal case in its closing remark); this drops normality for countable Γ, so it also kills non-normal witnesses such as (Γ, H) with H a non-normal copy of Z or of a finitely generated infinite group
  full-shift-full-group-kazhdan-subgroups-are-finite: that is the case H = Γ
---

**ESTABLISHED** by `wobbling-relative-t-subgroups-locally-finite-proof`.

## Statement

Let `W(Z)` be the group of bijections of `Z` of bounded displacement. For finite `Q ⊂ W(Z)` put
`r(Q) = max_{f∈Q} sup_n |f(n) − n|`. Let `Γ ≤ W(Z)` be a **countable** subgroup and `H ≤ Γ` **any**
subgroup such that `(Γ, H)` has relative property (T).

1. **(Window bound.)** For every `δ ∈ (0,1)` there are finite `Q ⊂ Γ` and `ε > 0` such that, with
   `L_0 = max(1, ⌈4 r(Q)/ε²⌉)`, every interval `I ⊂ Z` with `|I| = L ≥ L_0` has at most `2δ²L`
   points whose `H`-orbit is infinite or has more than `2L` points.
2. **(Bounded orbits.)** Every finitely generated `H' ≤ H` has uniformly bounded orbits on `Z`.
3. **(Local finiteness.)** Every finitely generated subgroup of `H` is finite.
4. **(Subset witnesses, necessary shape.)** If `X ⊂ Γ` is any subset such that every conditionally
   negative definite function on `Γ` is bounded on `X`, then for every `δ > 0` there is `L_0` such
   that `|xI Δ I| < δ² |I|` for every `x ∈ X` and every interval `I` with `|I| ≥ L_0`.

**Corollary.** Items 1–4 hold for every subgroup `Γ` of `[[X]]`, the topological full group of the
two-sided full shift, since `[[X]]` is countable and embeds in `W(Z)` through a dense `σ`-orbit.
In particular, no subgroup `Γ ≤ [[X]]` contains an infinite finitely generated subgroup, or an
element of infinite order, whose pair with `Γ` has relative (T).

## Role (class-kill, with the survivors named)

- **Class killed.** Every refutation of `full-shift-topological-full-group-is-a-t-menable` by a
  relative-(T) *subgroup* `H` that is not locally finite, normal or not. The shared invariant is that
  the interval vectors `|I|^{-1/2} 1_I` in `ℓ²(Z)` are almost invariant uniformly in the position of
  `I`. Every member dies at Step 4 of the proof: an orbit of a finitely generated subgroup with jumps
  at most `c` meets every run of `c` consecutive integers in its span. So a large orbit makes a
  `1/c` fraction of one window bad, against the `2δ²` bound.
- **Survivors.** Only two kinds of witness remain for a relative-(T) refutation of the Haagerup
  property of `[[X]]`, and so for this route to refuting `brin-thompson-groups-nv-are-a-t-menable`:
  - (S1) an infinite locally finite `H`, normal or not. The recorded candidate is
    `EL_2(F_p[t,t^{-1}]) ⋉ F_p[t,t^{-1}]²` (`full-shift-full-group-has-infinite-normal-relative-t-subgroup`).
    Non-normal locally finite `H` are not excluded either. No non-normal candidate is recorded.
  - (S2) a subset witness `X` generating no infinite relative-(T) subgroup. Cornulier's
    Example 1.12 (arXiv:math/0505193) shows that such witnesses exist in general:
    `SO_n(Z[2^{1/3}]) ⋉ Z[2^{1/3}]^n` for `n = 3, 4` is not Haagerup, has no infinite subgroup with
    relative (T), and has relative (T) with respect to a bounded subset of the lattice. Item 4 is the
    only constraint derived here on (S2).
- So this node does **not** prove the Haagerup property of `[[X]]`. The "TH alternative" (either
  Haagerup, or some infinite subset with relative (T)) is open in general, per Cornulier's
  introduction. Even granted it, (S2) is untouched.
