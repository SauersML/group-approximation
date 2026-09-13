---
rg: 2
id: burau-four-faithful-iff-faithful-on-brunnian-braids-proof
kind: route
title: "Brunnian reduction for 4-strand Burau: Long's theorem applied to the noncentral normal subgroup Brun_4"
target: burau-four-faithful-iff-faithful-on-brunnian-braids
requires:
  - burau-faithful-iff-faithful-on-noncentral-normal-subgroup
  - brunnian-four-braids-are-pseudo-anosov
---

`Brun_4` is normal in `B_4`, nontrivial, and meets `Z(B_4) = ⟨Δ²⟩` trivially. So it is not
contained in the center (part 1 of `brunnian-four-braids-are-pseudo-anosov`). Long's theorem
(`burau-faithful-iff-faithful-on-noncentral-normal-subgroup`, `n = 4`) says `ρ_4` is faithful iff
it is faithful on `Brun_4`, i.e. iff `ker ρ_4 ∩ Brun_4 = 1`. ∎
