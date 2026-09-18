# Referee report (gq-referee-c): brin-thompson-first-return-maps-lie-in-kv

- **Node:** `research/brin-thompson-first-return-maps-lie-in-kv.md` and its `-proof` route, landed 9e5998ab5 by
  lane `gq-nv-obstruct`.
- **Lens:** independent re-derivation. It is an input of the BS(1,3) ≤ 3V chain.
- **Verdict: PASS.**

## Re-derivation

The hypothesis is that every point enters `Y` within `R` steps: `C^k = ⋃_(0<=i<=R) T^(-i) Y`.

**Item 1.**
- *Bounded return.* For `y ∈ Y`, apply the hypothesis to `Ty`. This gives `r_Y(y) <= R+1`. The sets
  `Y_r = Y ∩ T^(-r)Y \ ⋃_(0<i<r) T^(-i)Y` are clopen and partition `Y`.
- *Injective.* Take `y ∈ Y_r` and `y' ∈ Y_s` with `r < s` and `T^r y = T^s y'`. Then `T^(s-r) y' = y ∈ Y` with
  `0 < s-r < s`, which contradicts the minimality of `s`. ✓
- *Surjective.* Given `z ∈ Y`, the hypothesis at `T^(-(R+1)) z` gives a least `t ∈ [1, R+1]` with
  `T^(-t) z ∈ Y`. Minimality of `t` gives `r_Y(T^(-t) z) = t`, so `T_Y(T^(-t) z) = z`. ✓
- *Homeomorphism.* `T_Y` is a continuous bijection of the compact Hausdorff space `Y`. ✓

**Item 2.**
- *Brick-local.* On `Y_r`, `T_Y = T^r ∈ kV`, and `Y_r` is a finite union of bricks. After refining, `T_Y` is a
  prefix replacement on each brick of a finite partition of `Y`. ✓
- *The conjugator ψ exists.* `Y` is a finite disjoint union of bricks `B_1, …, B_s`, because bricks form a clopen
  basis closed under intersection and `Y` is compact. `C^k` splits into `s` bricks `D_i` by repeated halving.
  Map `B_i -> D_i` by the prefix replacement between them. ✓
- *The conjugate lies in kV.* Composites of brick-local maps are brick-local. Refine so that each piece lands in
  one brick of the next map: intersections of bricks are bricks, and the preimage of a sub-brick under a prefix
  replacement is a sub-brick. So `ψ T_Y ψ^(-1)` is a bijection of `C^k` that is a prefix replacement on a finite
  brick partition. Hence it lies in `kV`. This holds for every brick-local `ψ`. ✓

## Calibration

- **Where the bounded-return hypothesis enters.** Bounded return is what makes `T_Y` a finite union of the pieces
  `T^r|_(Y_r)`. Without it the partition `{Y_r}` is infinite, and the argument gives no finite brick partition.
- **In the chain:** `R = 5` for SMART's `Y`, by `smart-induced-on-genuine-moves-has-exact-tripling`, item 1. My
  report on that node checks this.
