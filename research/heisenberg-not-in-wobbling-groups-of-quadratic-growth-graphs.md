---
rg: 2
id: heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs
kind: claim
title: "H_3(Z) acts faithfully by bounded displacement on no graph of uniformly quadratic growth, so it lies in no topological full group of a Z^2-action; and sub-N^(1/d) distorted elements lie in no wobbling group of degree-d growth"
distinct_from:
  heisenberg-group-lies-in-no-z-subshift-elementary-group: that excludes H_3 from linear groups over Z-subshift crossed products by stable length; this excludes H_3 from permutation groups whose orbits have quadratic growth, where c is not excluded by stable length (|c^N| ~ sqrt(N) is exactly the borderline).
  subshift-crossed-product-gl-has-no-distorted-elements: that is a Krylov/propagation argument over a Z-crossed product; this is a box count in orbit graphs that uses a second commuting direction.
  thompson-f-does-not-embed-in-wobbling-groups-of-recurrent-graphs: that excludes F from recurrent wobbling groups by transience; this excludes H_3 (amenable, polynomial growth) by counting.
  heisenberg-in-nv-forces-drift-free-central-element: that is a measure/drift condition on H_3 inside nV; this is a growth condition on the orbit graphs of an H_3 action.
---

**ESTABLISHED (unreviewed).** Route: `heisenberg-not-in-wobbling-groups-quadratic-box-count-proof`.

**Setting.** `Γ` is a graph on a vertex set `V` with path metric `d` (distance `∞` between
components). `W(Γ)` is the group of bijections `g` of `V` with `sup_v d(v, g v) < ∞`. The integer
Heisenberg group is `H = ⟨a, b⟩` with `c = [a, b]` central of infinite order.

**Statement.**
1. **(Quadratic hosts.)** Suppose `|B(v, r)| ≤ C r^2` for all `v ∈ V` and integers `r ≥ 1`. For
   every homomorphism `ρ : H → W(Γ)` let `K` be the largest displacement of `ρ(a)`, `ρ(b)`. Put
   `s_0 = ⌈169 C K^2⌉`. Then every `⟨ρ(c)⟩`-orbit has at most `s_0^2` points. So `ρ(c)^M = 1`
   with `M = lcm(1, ..., s_0^2)`, and `ρ` is not injective. No group containing `H` acts faithfully
   by bounded displacement on such a graph; this includes `SL_n(Z)` for `n ≥ 3`.
2. **(Full groups of quadratic-growth actions.)** Let `P` be a group with finite symmetric
   generating set `T` and `|B_P(r)| ≤ C r^2`, such as `P = Z^2`. Let `P` act on a set `X`. Then `H`
   is not a subgroup of `[[P ↷ X]]`, the group of bijections `g` of `X` with a finite `F ⊆ P` such
   that `g x ∈ F x` for all `x`. This covers topological full groups of all `Z^2`-subshifts. It
   also covers the product action `σ × σ` on `({0,1}^Z)^2`, whose full group maps into `4V` when
   each copy of `{0,1}^Z` is coded by two one-sided halves as in Salo's baker's-map coding. That
   remark is not used in any proof here.
3. **(Polynomial hosts, any distortion.)** Suppose `|B(v, r)| ≤ C r^d` for all `v` and `r ≥ 1`,
   `G = ⟨S⟩ ≤ W(Γ)` is finitely generated, and `g ∈ G` has `|g^N|_S = o(N^(1/d))`. Then `g` has
   finite order. So `BS(1, k)` with `k ≥ 2` (where `|a^N| = O(log N)`) lies in no such `W(Γ)`.
   Neither does any finitely generated group containing the Callard–Salo element `f ∈ mV` with
   `|f^N| = O(log^4 N)` (`brin-thompson-mv-contains-a-distortion-element`).

**Sharpness.** Item 1 fails for cubic growth, at least at the counting step.
- The Schreier graphs `X_L = H / ⟨a, b^L, c^L⟩` on `(Z/L)^2` have the moves
  `b:(t,u) ↦ (t+1,u)`, `c:(t,u) ↦ (t,u+1)` and `a:(t,u) ↦ (t,u+t)`.
- The disjoint union over `L` is a faithful `H`-set.
- Its balls grow like `0.72 r^3` up to scale `√L`
  (`experiments/heisenberg-quadratic-growth-hosts-2026-09-17/output.txt`).
- Whether `H` embeds in `W(Z^3)`, or in `[[Z^3 ↷ X]]`, is open.

**What it kills (for `heisenberg-group-embeds-in-some-brin-thompson-group`).**
- **Class:** every construction of `H ≤ mV` in which `H` moves points inside the orbits of a
  quadratic-growth group by uniformly bounded jumps. Members are topological full groups of
  `Z`- and `Z^2`-subshifts, product-shift full groups `[[Z^2 ↷ ({0,1}^Z)^2]] ≤ 4V`, and head
  motions on 2D tapes with injective position.
- **Invariant:** the growth of the orbit graphs against the quadratic distortion of `c`.
- **Where every member dies:** the box `{a^s c^u v : 0 ≤ s ≤ s_0, 0 ≤ u < R^2}` lies inside a
  ball of radius `13KR`, which holds too few points. This forces short stabilizer elements
  `a^σ c^μ` and `b^τ c^ν`, and their commutator `c^(στ)` fixes the orbit.
- **What survives:** hosts whose orbit graphs have growth at least `r^3`, including the
  exponential-growth orbits of reversible Turing machine groups inside `mV`.
