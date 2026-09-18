---
rg: 2
id: quadratic-rotation-iet-groups-satisfy-boone-higman-proof
kind: route
title: IET(Z + alpha Z) is the full group of the Sturmian rotation, which is substitutive for quadratic alpha
target: quadratic-rotation-iet-groups-satisfy-boone-higman
requires:
  - substitution-subshift-full-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

1. **Cantor model.** Let `X_α` be `[0,1)` with every point of the orbit `Λ mod 1`
   doubled into a left and a right copy. Rotation `R_α` lifts to a minimal
   homeomorphism of the Cantor set `X_α`, conjugate to the Sturmian subshift of slope
   `α` (standard). In `X_α`, every interval `[x,y)` with `x, y ∈ Λ` is clopen, and
   every clopen set is a finite union of such intervals.
2. **IET(Λ) ≤ [[R_α]].** Let `f ∈ IET(Λ)` have pieces `[x_i, x_{i+1})` with
   translation `t_i ∈ Λ`. Write `t_i ≡ n_i α (mod 1)` with `n_i ∈ Z`. Then `f` agrees
   with `R_α^{n_i}` on `[x_i, x_{i+1})`. Its lift to `X_α` is a homeomorphism that is
   locally a power of `R_α`, so it lies in `[[R_α]]`. The lift is injective on
   `IET(Λ)`.
3. **Substitutive.** For quadratic `α` the Sturmian subshift of slope `α` is a
   primitive aperiodic substitution subshift. This is the standard characterization
   (cited, not read at source): its continued-fraction directive sequence is
   eventually periodic, so after telescoping its Bratteli–Vershik model is stationary.
4. **Conclude.** `substitution-subshift-full-groups-satisfy-boone-higman` embeds
   `[[R_α]]`, and hence `IET(Λ)`, in a finitely presented simple group.
