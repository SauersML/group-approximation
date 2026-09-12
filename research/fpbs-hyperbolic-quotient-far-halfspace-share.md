---
rg: 2
id: fpbs-hyperbolic-quotient-far-halfspace-share
kind: claim
title: Far halfspaces of a hyperbolic quotient carry a vanishing share of the subcritical cluster
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**OPEN.** Let `Gamma` be finitely generated with an infinite normal subgroup
`H` such that `Q = Gamma/H` is non-elementary word hyperbolic. Let `S` be a
finite symmetric generating set and `Phi : Q -> H^d` a rough similarity onto a
coarsely dense subset of a closed convex set. Then

```text
lim_{D -> infinity}  sup_{p<p_c} sup_{a in Q} sup_{halfspaces H of H^d, d(Phi(a),H) >= D}
    chi_p^(-1) E_p| K_(s(a)) ∩ pi^(-1)(Phi^(-1) H) |  =  0,
```

where `s(a)` is any lift of `a`. This is premise (ii) of
`fpbs-hyperbolic-quotient-fibre-estimates-l2-gap`. For `H` trivial it is
Hutchcroft's Lemma 5.4 (arXiv:1804.10191), proved there with nested roughly
branching barriers.

## Attempts

* **Lift Hutchcroft's branching barriers.** A barrier between `o` and a
  fibre-saturated halfspace must contain whole fibres, so its capacity is a sum
  of fibre sums. Hutchcroft bounds barrier capacity by supermultiplicativity of
  `tau`, and fibre sums are not supermultiplicative: products of lifts collide
  in `H`. What survives, for central `H = <z>`, is weaker:
  * fibre maxima over a roughly branching set sum to at most 1;
  * height windows of width `W` have capacity at most `2W+1`.

  **Where it dies:** neither bounds a full-fibre barrier.
* **Tree-projected generating sets of `F_n x Z`.** Fibres are cut sets, and
  sequential BK gives a branch share at depth `D` of at most
  `(max_s sigma_p(s))^D`. So the claim follows from
  `sup_{p<p_c} max_s sigma_p(s) < 1` (artifact Section 4.3). **Where it stops:**
  that nearest-fibre bound is open.
* **l2 control of the profile.** Square summability of `sigma_p`
  (`fpbs-hyperbolic-quotient-uniform-fibre-bubble`) does not control l1 mass on
  halfspaces, which contain exponentially many cosets. **Where it dies:** no
  interpolation passes from l2 to halfspace l1 shares.
* **First-entry decomposition.** BK at the first vertex of an open path in the
  separating set `pi^(-1)(d_in H_Q)` gives
  `E_p|K_o ∩ pi^(-1)(H_Q)| <= chi_p sum_{q in d_in H_Q} sigma_p(q)`. So the share
  is at most the fibre mass of the inner boundary. **Where it stops:** that
  boundary is an infinite set of cosets, and nothing bounds its mass.
* **Bypass through rapid decay.** On the route
  `fpbs-hyperbolic-quotient-via-weighted-fibre-bubble` this premise is not needed.
  A polynomially weighted critical fibre bubble bounds `||T_(p_c)||` directly
  through the rapid decay inequality on `Q`
  (`fpbs-rd-quotient-weighted-bubble-gives-critical-l2`). **Where it stops:** this
  claim itself remains open. The bypass only removes it from one route.
