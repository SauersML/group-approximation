---
rg: 2
id: depth-monotone-configurations-cannot-force-ternary-minus-one
kind: claim
title: No weakly finite certificate for the ternary Leavitt target has all its group elements in a subgroup conjugate into the units of a depth-monotone Leavitt subalgebra, and the mismatched pair T_(0,1), T_(1,00) lies in one
distinct_from:
  anti-central-sofic-data-cannot-force-defect-submultiplicativity: that realizes anti-central data on sofic subgroups; this places the depth-mismatched transvection configurations in explicitly locally residually finite subgroups with an explicit weakly finite model, so that firewall applies to them.
  graphs-of-locally-finite-groups-carry-regular-rank-models: that realizes the pair T_(0,1), T_(1,00) over F_2 in a rank model of a graph of locally finite groups, keeping the cylinder defect nonzero but only vertex-group relations; this realizes every relation of an actual subgroup of the ternary unit group containing the pair, with z -> -1, and sends the defect to 0.
  sofic-configurations-cannot-force-v-rank-triviality: that is the rank firewall for sofic configurations of Thompson's V; this is the weakly finite firewall for configurations of Leavitt units whose transvections change depth in one direction for some letter weight.
artifacts:
  - research/artifacts/depth-monotone-leavitt-firewall-2026-09-12.md
---

**ESTABLISHED** by `depth-monotone-minus-one-firewall-proof` (artifact Section 3). Independently re-derived by
`w4-vf-gate`, Section 30.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`.

Let `G = L_(F_3)(1,2)^x`, `z = -1` and `ε_- = 2(1 - [z])`. Let `Γ_0 <= G` contain `z`. Suppose some `u in G` and
some weight `ω` put `u Γ_0 u^(-1)` inside `(R^ω_≤)^x` or `(R^ω_≥)^x`, as in
`depth-monotone-leavitt-subalgebras-are-stably-finite`. Then `ε_- F_3[Γ_0]` has a nonzero weakly finite image.
So no finite certificate for `ternary-anti-central-summand-has-no-weakly-finite-image` has all its group
elements in `Γ_0`.

**Proof.** The stably finite embedding gives a unital ring map `F_3[Γ_0] -> Q` with `[z] -> -1`, so
`ε_- -> 1`. A weakly finite target kills the whole reflection ideal and not `1`. Every such `Γ_0` is sofic,
so this also follows from `linear-sofic-group-algebra-is-stably-finite`; the content is the placement.

**Configurations covered** (standard grading, `a = b`):
- `z`, the sign group `E`, the level part of `V`, and all degree-zero units `∪_n GL_(2^n)(F_3)`;
- every transvection `T_(σ,κ)(λ)` with `|σ| <= |κ|`: all level root elements at every depth, `w_0`, and the
  depth-decreasing `T_(1,00)`;
- the mismatched pair `T_(0,1) = 1 + A`, `T_(1,00) = 1 + B` with `A^2 = B^2 = 0`, `AB = s_0 t_00`,
  `BA = s_1 t_10`, and product `1 + A + B + AB`. The relations in `W` that this lane was asked to compute hold
  in the model, so they give neither a one-sided pair nor a contradiction with `z = -1`.

Weight `b = 2a` adds `{T_(0,1), T_(1,00), T_(00,1)}`. The opposite side at `a = b` covers
`{T_(0,1), T_(1,0), T_(00,1)}`.

**What it does not cover.**
- The models send the two-root defect `D` to `0` when both roots lie inside. So they do not firewall
  `ternary-weakly-finite-representations-kill-two-root-defect` read on `Γ_0`.
- `{T_(0,1), T_(1,0), T_(1,00), T_(00,1)}` and the non-level elements of `V` lie in no `(R^ω_≤)^x` and no
  `(R^ω_≥)^x` (artifact Section 4). Conjugation can still flatten a configuration, as it does for
  `{T_(10,0), T_(0,10)}`, so escaping is not yet a criterion.
