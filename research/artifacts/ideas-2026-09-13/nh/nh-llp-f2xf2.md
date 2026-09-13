# Idea lane nh-llp-f2xf2: the LLP of C*(F2×F2) as a route to a non-hyperlinear group

Lens: Kirchberg's local lifting property for `C*(F2×F2) = C*(F2) ⊗max C*(F2)`
(Fournier-Facio–Willett Question 1.6). By `sp2g-z-full-c-star-algebra-has-llp` it is
a necessary step on our Sp4 route, since `F2×F2 ≤ Sp4(Z)` and LLP passes to full
C*-algebras of subgroups.

This is an idea file, not a claim. Nothing here is established and no node status
changes. Each approach records the idea, what it would give, the cheapest kill test,
the result of running that test, and a verdict.

Repo context read first:
- `non-hyperlinear-group`: the existence compression and literature boundary section.
- `llp-non-rf-kazhdan-group-is-non-hyperlinear` and
  `non-rf-kazhdan-weak-ucp-iff-non-hyperlinear`: a non-RF Kazhdan group is
  non-hyperlinear iff it is weakly ucp-stable.
- `llp-implies-weak-ucp-stability`.
- `harris-lp-is-maximal-matrix-range-collapse`: LP of an explicit three-dimensional
  Harris system is equivalent to LLP of the ambient algebra, and holds iff the
  scaling constant `γ = 1`.
- `maslov-generator-complete-order-model-is-llp-strength`: the single-pattern
  weakening is already full-LLP strength. It is not repeated here.

## 1. The Haagerup fence: LLP permanence seeded by F2×F2 never reaches a Kazhdan group

**Idea.** Every operation known to preserve LLP of full group C*-algebras keeps us
inside groups with the Haagerup property:
- passing to subgroups (conditional expectation from the positive definite function `1_Λ`);
- free products amalgamated over finite subgroups (LLP: Pisier, extended by Ozawa over
  finite-dimensional subalgebras);
- direct products with amenable groups (tensoring with a nuclear algebra);
- directed unions.

`F2×F2` has the Haagerup property, and an infinite group cannot have both the
Haagerup property and property (T). So no LLP-permanence chain starting from
`C*(F2×F2)` produces an infinite Kazhdan group. The only LLP transfer that can create
rigidity is a locally split quotient map `C*(F_n) → C*(Λ)`, and that is the
definition of LLP for `C*(Λ)`, not a reduction.

**Payoff.** A fence, not a theorem. A positive answer to Question 1.6 can feed
`llp-non-rf-kazhdan-group-is-non-hyperlinear` only through a genuinely new transfer
principle that is not an LLP permanence. The Sp4 containment runs the wrong way:
LLP(Sp4) ⇒ LLP(F2×F2), not the converse.

**Kill test run.**
- Antolín–Dreesen (arXiv:1305.6748, abstract): the Haagerup property "is not
  preserved under arbitrary group extensions and amalgamated free products over
  infinite groups, but it is preserved under wreath products and amalgamated free
  products over finite groups."
- Not re-read in this lane: permanence under subgroups, direct products, directed
  unions, and extensions with amenable quotient (the standard permanence list of
  Cherix–Cowling–Jolissaint–Julg–Valette). These have to be checked against source
  before the fence is landed as a claim.
- Crossed-product-type LLP transfers are deliberately left out of the operation list
  above, because Haagerup permanence fails for general extensions: `Z²⋊SL2(Z)` has
  relative property (T).

**Verdict: killed as a route to a non-hyperlinear group.** Survives as a partial fence.

## 2. Max-tensor scaling of Harris matrix ranges

**Idea.** `C*(F2)` has the LP, so the Harris systems built from its two free unitary
generators have scaling constant `γ = 1` in the sense of
`harris-lp-is-maximal-matrix-range-collapse`. For each factor, choose finite free
spectrahedra approximating the factor's matrix range within `1 ± ε`. The goal is a
product inequality

```text
γ(T_A ⊗max T_B) <= f(γ(T_A), γ(T_B)),   f(1,1) = 1,
```

for the self-adjoint pair built from the four generators of `C*(F2×F2)`, using the
intersection of the two factor spectrahedra as the candidate approximant.

**Payoff.** LP of the Harris system of `C*(F2×F2)`, hence LLP of `C*(F2×F2)`, which
is the LLP half of Question 1.6. This alone is still not LLP of `C*(Sp4(Z))`.

**Kill test run.**
- Literature: searched scaling constants and tensor products of matrix convex sets
  (Passer–Shalit–Solel, "Shape, scale, and minimality of matrix ranges",
  arXiv:1803.09212). No product formula for `γ` under ⊗max was found.
- Structural: the Harris system of `A ⊗max B` is not the tensor product of the factor
  systems. Hyperrigidity of a tensor-type system inside the max tensor product is not
  automatic either.
- If the inequality held for all LP algebras `A`, `B`, then LLP would pass to ⊗max of
  any two LP algebras. That question appears to be open (Enders–Shulman
  arXiv:2403.12224 and the surrounding literature), so this test does not refute the
  idea. It only says the idea cannot be cheap.

**Next cheapest test (not run).** An SDP lower bound for `γ_2` of the four-generator
Harris pair at matrix level 2, with NPA-type upper bounds for max-norm quantities.
MSI-light.

**Verdict: unclear.** Bold, not refuted, no supporting source found.

## 3. Ext as a group by interleaving the two lifts

**Idea.** Enders–Shulman (arXiv:2403.12224, abstract): for a class including
`C*(F_n×F_n)`, "the LLP is equivalent to Ext being a group". An extension
`τ : C*(F2×F2) → Q(H)` is a pair of essentially commuting representations of
`C*(F2)` in the Calkin algebra. Each side lifts ucp, because `C*(F2)` has the LP.

Take Stinespring dilations `π_1, π_2` of the two lifts. Using a quasicentral
approximate unit for the C*-algebra generated by the images and the compacts (the
Arveson / Kasparov technical theorem), cut both dilations into alternating blocks so
that `π_1` and `π_2` commute exactly between different blocks. The joint ucp lift
would be the compression of the resulting pair.

**Payoff.** Every extension of `C*(F2×F2)` is semisplit, so Ext is a group and
`C*(F2×F2)` has the LLP.

**Precise gap.** Interleaving makes the cross terms between blocks compact, not zero.
Positivity of the joint map on `M_k(E)`, for `E` a finite-dimensional operator
subsystem of `C*(F2) ⊗max C*(F2)`, needs an *exactly* commuting pair of dilations.
Product-type (min-norm) constructions cannot supply one, since `⊗min ≠ ⊗max` here
after MIP* = RE. So the construction has to produce genuine commuting dilations, and
this is exactly where the open question lives.

**Kill test run.** Structural, as in approach 2. The argument never uses anything
specific to `F2`, so for all LP pairs it is equivalent to the open preservation
question. It is not refuted. The special case where one side of `τ` lands in a nuclear
C*-subalgebra of `Q(H)` modulo compacts follows from Choi–Effros, but that case is
trivial.

**Verdict: unclear.** The gap above is where a new idea is needed.

## 4. Automatic lifting through tracial ultraproduct quotients

**Idea.** Instead of LLP of the source algebra, try to obtain weak ucp-stability of a
non-residually-finite Kazhdan group from a general lifting theorem for the quotient
map `∏ M_{d_n} → ∏^ω M_{d_n}` (tracial ultraproduct), in the style of Choi–Effros or
Effros–Haagerup.

**Kill test run (hand argument plus repo).**
- The kernel `J_ω = {x : lim_ω ||x_n||_2 = 0}` is not exact. Choose projections `p_n`
  of rank `r_n` with `k_n r_n / d_n → 0` and `k_n → ∞`. Then `y ↦ (y_n ⊗ p_n)` embeds
  `∏ M_{k_n}` into `J_ω`. That product contains `C*(F2)`, which is residually finite
  dimensional (Choi) and not exact (Wassermann). Both are standard facts, not re-read
  in this lane.
- More decisively: any such automatic theorem would make *every* group weakly
  ucp-stable. That includes Thom's Connes-embeddable non-RF Kazhdan groups, recorded
  in `llp-non-rf-kazhdan-group-is-non-hyperlinear`. For those groups
  `non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` would then force non-hyperlinearity,
  which is a contradiction.

**Verdict: killed.** The input to weak ucp-stability has to be group-specific: LLP of
the source algebra or a stability property of the group. It cannot be a property of
the tracial ultraproduct quotient alone.

## Reformulation noted, not pursued

Kirchberg's theorem, LLP(A) ⇔ `A ⊗min B(H) = A ⊗max B(H)`, together with the fact
that `(C*(F2), B(H))` is a nuclear pair, gives

```text
LLP(C*(F2×F2))  <=>  (C*(F2) ⊗max C*(F2)) ⊗min B(H) = C*(F2) ⊗max (C*(F2) ⊗min B(H)).
```

That is, min and max associate for the triple `(C*(F2), C*(F2), B(H))`. It is only
Kirchberg's theorem restated. It becomes testable only with a triple where these norms
are computable, for example the expander elements of arXiv:math/0110151.

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | Haagerup fence on LLP permanence from F2×F2 | killed as a route, partial fence (permanence list still to verify) |
| 2 | Max-tensor scaling of Harris matrix ranges | unclear (no product formula found; SDP test proposed) |
| 3 | Ext-group interleaving of the two lifts | unclear (gap: exactly commuting dilations) |
| 4 | Automatic lifting through tracial ultraproduct quotients | killed (Thom's hyperlinear non-RF Kazhdan groups) |
