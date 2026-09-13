---
rg: 2
id: titz-witzel-lattices-pbh-from-mif-kernels
kind: route
title: MIF kernels put the Titz Mite--Witzel lattices in the type (A) class through BFFHZ Theorem C
target: titz-witzel-lattices-satisfy-permutational-boone-higman
requires: [titz-witzel-kernels-are-mif, fp-simple-highly-transitive-groups-satisfy-pbh, boone-higman-type-a-class-closed-under-finite-extensions, titz-witzel-simple-kazhdan-cat0-lattices-exist]
---

Fix `i, q` and write `Γ = Γ_i^q` and `Γ̌ = Γ̌_i^q`.

1. **`Γ̌` is finitely presented and simple.**
   - **Finite index.** By `titz-witzel-simple-kazhdan-cat0-lattices-exist`
     (Titz Mite--Witzel Theorem A, arXiv:2509.05054v2 TeX l.197), `Γ` is the
     fundamental group of the finite triangle complex `Y_i^q`, so it is
     finitely presented, and "the finite residual `Γ̌_i^q` has finite index".
   - **Finite presentation.** A finite-index subgroup of a finitely presented
     group is finitely presented (Reidemeister--Schreier, standard).
   - **Simplicity.** `Γ̌` is simple by their Corollary (TeX l.201--203).
2. **`Γ̌` lies in `B_A`.** `Γ̌` is MIF by `titz-witzel-kernels-are-mif`. BFFHZ
   Theorem C, imported as `fp-simple-highly-transitive-groups-satisfy-pbh`,
   says every finitely presented simple MIF group satisfies the permutational
   Boone--Higman conjecture, so `Γ̌ ∈ B_A`.
3. **`Γ` lies in `B_A`.** By item 2 of
   `boone-higman-type-a-class-closed-under-finite-extensions`, `B_A` is closed
   under finite-index overgroups.
4. **Envelopes.** By item 3 of the same claim, every subgroup of `Γ` embeds in a
   finitely presented simple group. `∎`
