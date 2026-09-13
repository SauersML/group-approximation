---
rg: 2
id: expander-matching-no-hyperbolic-instance-proof
kind: route
title: Infinite Kazhdan subgroups are non-elementary, and centralizers of non-elementary subgroups are finite
target: expander-matching-mechanism-has-no-hyperbolic-instance
requires:
  - hyperbolic-nonelementary-centralizer-finite
---

**Step 1 (Γ is non-elementary).** An elementary subgroup of a hyperbolic group
is finite or virtually infinite cyclic. `Γ` is infinite, so an elementary `Γ`
would be virtually infinite cyclic, hence infinite amenable. An infinite
amenable group does not have property (T). This is the first rider recorded on
`hyperbolic-nonelementary-centralizer-finite`. So `Γ` is non-elementary.

**Step 2 (J is finite).** `[Γ, J] = 1` means `J <= C_G(Γ)`. By
`hyperbolic-nonelementary-centralizer-finite`, `C_G(Γ)` is finite, so `J` is
finite.

**Consequence 1.** A finite group `J` is LEF: for every finite `F <= J`, the
inclusion `F -> J` is an injection into a finite group that respects every
product lying in `F`. So a Proposition 2.3 configuration inside a hyperbolic
group has LEF commuting factor, and the criterion yields no contradiction.

**Consequence 2.** If `Γ × J` with both factors infinite and `Γ` Kazhdan sat
inside a hyperbolic group `G`, then `J <= C_G(Γ)` would be infinite,
contradicting Step 2. Subgroups of `G` inherit the configuration, so no group
containing such a product embeds in any hyperbolic group. For
`EL_D(R)`, the product `Γ × J` with `J ≅ V` infinite is the configuration of
counterexample.tex Section 3.
