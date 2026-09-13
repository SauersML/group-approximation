---
rg: 2
id: four-transvection-set-escapes-depth-monotone-units
kind: claim
title: The span of the four transvections at cylinders 0, 1 and 00 is not directly finite, so no conjugate of their group lies in any depth-monotone unit group, while every three of them lie in one
distinct_from:
  depth-monotone-configurations-cannot-force-ternary-minus-one: that firewalls configurations lying inside one weighted unit group; this shows that S4, and every group containing x_0, lie in no conjugate of any such group, so that firewall never applies to them.
  lex-decreasing-units-with-order-preserving-letters-are-amenable: that makes groups built from lexicographically decreasing units and order-preserving letters amenable; S4 contains both T_(0,1) and T_(1,0) and generates a nonamenable group, and this claim is a conjugation invariant, not an amenability statement.
artifacts:
  - research/artifacts/four-transvection-escape-set-2026-09-12.md
---

**ESTABLISHED** (artifact Section 1, route `four-transvection-escape-proof`). Verified by `w4-vf-gate` in Section 36.1
of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`, PASS with no corrections.

**Statement.** Let `R = L_K(1,2)` over any field `K`, `T_(σ,κ) = 1 + s_σ t_κ`, and
`S4 = {T_(0,1), T_(1,0), T_(1,00), T_(00,1)}`. For a weight `ω`, `H^ω_≤` and `H^ω_≥` are the unit groups of the
spans of the `s_μ t_ν` with `ω(μ) <= ω(ν)`, respectively `ω(μ) >= ω(ν)`.
1. The span of `<S4>` contains `x = s_00 t_0 + s_1 t_1` and `y = s_0 t_00 + s_1 t_1`, with `yx = 1` and
   `xy = 1 - s_01 t_01 != 1`.
2. So for every unit `u` and every weight `ω`, `u<S4>u^(-1)` lies in neither `H^ω_≤` nor `H^ω_≥`.
3. Every three-element subset of `S4` lies in some `H^ω_≤` or `H^ω_≥` without conjugation (weights `a = b` or
   `b = 2a`). So `S4` is a minimal escaping set of transvections.
4. If `u g u^(-1)` lies in the span for `≤` (respectively `≥`), then `π(g)` (respectively `π(g*)`) is locally finite
   on the cylinder functions. `x_0 = s_0 t_00 + s_10 t_01 + s_11 t_1` fails this on both sides, since
   `π(x_0) 1_[1^n] = 1_[1^(n+1)]` and `x_0* = x_0^(-1)`. So no conjugate of any group containing `x_0` lies in a
   depth-monotone unit group.

**Consequence.** This is the conjugation invariant that the `w6-mismatch-c3` Attempts entry on
`ternary-leavitt-units-have-no-weakly-finite-representation` found missing. A subgroup escapes the depth-monotone
firewall under every conjugation as soon as its span holds a one-sided inverse pair that is not two-sided, or it
contains an element that acts on cylinder functions without being locally finite.

**Scope.** Escaping this firewall is not escaping all of them: `four-transvection-units-have-a-weakly-finite-symbol-image`
gives `<S4>`, and every five-transvection set of the form `S4 ∪ {T}`, a weakly finite model with `z -> -1`. Other
five-transvection sets are not covered.
