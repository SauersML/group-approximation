---
rg: 2
id: subshift-f2-ring-indicator-ideals-and-centreless-el3
kind: claim
title: Over a minimal subshift ring, an ideal containing a clopen indicator is everything, and EL_3 over F_2 is centreless
---
Let `X ⊆ A^Z` be an infinite minimal subshift with shift `T`, and let `R = LC(X,F_2) ⋊_T Z`, with `u f u^{-1} = f∘T^{-1}`. Write `e_W` for the indicator of a clopen set `W`.

1. Every two-sided ideal of `R` that contains `e_W` for some nonempty clopen `W` is `R`.
2. `Z(EL_3(R)) = {1}`. The proof uses only that `T` has no periodic points, together with `F_2^× = {1}`. Minimality is not used.

**Why it matters.** These are the only ring-level facts that the simplicity proof in `simple_kazhdan_sofic_group.tex` (disk version of 16:46) needs:
- The level ideal `I_N = {r : e_12(r) ∈ N}` contains some `e_W`, so fact 1 can replace the simplicity of `R`. It also replaces the citations to Brown–Clark–Farthing–Sims, Clark–Edie-Michell and Steinberg (disk l.102–109 and l.226).
- Fact 2 replaces the computation `Z(R) = F_2` (disk l.110–116).

Over `F_q` with `q > 2`, fact 2 needs one more step: commuting with `e_ij(u)` makes the invertible function `c` `T`-invariant, hence constant by minimality, and then `c` is a scalar.

**Status:** established (folklore); see the direct proof route.
