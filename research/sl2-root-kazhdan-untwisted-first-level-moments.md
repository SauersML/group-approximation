---
rg: 2
id: sl2-root-kazhdan-untwisted-first-level-moments
kind: claim
title: For the untwisted Kazhdan SL_2 root triangle with q = 8, no nonzero edge twist splits over ker(Λ_0 -> SL_2(64)), whose mod-2 first homology has dimension 18
distinct_from:
  sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2: that constructs the vertex-injective map onto SL_2(q^2); this computes the mod-2 homology and edge-twist moments of its kernel for q = 8
---

**Setting.** `Λ_0` is the untwisted member of `kazhdan-hyperbolic-sl2-root-triangles` with `q = 8`.
The field is `F_64 = F_2[x]/(x^6 + x + 1)`, and `s` is the class of `x`. `ρ: Λ_0 -> SL_2(64)` comes from
`sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2`, and `N = ker ρ` is torsion-free. The images of
the edge groups are `E_12 = { [[1+Px, P^2x],[x, 1+Px]] }`, `E_13 = u(F_8)` and `E_23 = v(sF_8)`, with
`P^2 = 1/s`.

**ESTABLISHED (computer-assisted; unreviewed).**
- **The complex.** `N\X` has `1041` vertices, `98,280` edges and `262,080` triangles, so
  `χ = 164,841`.
- **Homology.** `rank_{F_2} B = 97,222`, where `B` is the matrix of right-coset indicators. Hence
  `b_2(N;F_2) = dim Z_N = 164,858` and `b_1(N;F_2) = 1 + b_2 - χ = 18`.
- **Moments.** Adding the moment rows raises the rank to `97,231`. By
  `edge-twist-moment-test-elementary-abelian-edges`, `I_N = F_2^9`, the whole twist space
  `⊕_e Hom(E_e, F_2)`.
- **Consequence.** No nonzero edge-twisted central extension of `Λ_0` has a finite quotient injective on
  the center that factors through `C^Q ⋊ Q` at this level. Deeper levels can only shrink the moment space
  `I_N` (M4').

**Calibration (independent check).** The same script for the untwisted `q = 4` member
(`Q = SL_2(16)`) gives `b_1(N;F_2) = 20` and `dim I_N = 6 = 3f`. GAP's Reidemeister–Schreier
computation of `H_1(ker;Z)` for that kernel returns `(Z/2)^11 × (Z/4)^9`: twenty even invariants, which
agrees (`run3.out`).

**Reading, not established.**
- `18 = dim_{F_2} sl_2(F_64)`, and `20 = 12 + 8` would be adjoint plus natural module for `q = 4`. This
  suggests that the first 2-covers of `N` are adjoint congruence covers, through `SL_2(F_64[t]/t^2)`.
- There `R = N/N''` is elementary abelian of rank up to 18, with plenty of 2-torsion in `H_2(R;Z)`. By the
  Cartan–Leray filter of `hyperbolic-triangle-colimit-with-persistent-edge-twist`, this is the first
  place where a moment could die.
- `SL_2`-invariant quadratic forms on `sl_2(F_64)`, such as `X ↦ tr_{F_64/F_2} det X`, give central
  extensions of such covers. They are the natural test for whether it does.

**Scope.** `Λ_0` is virtually torsion-free, so it is not a quotientless candidate. The data concern the
persistence route: a twist that survives every cover would make the hyperbolic Kazhdan group `Λ_{0,c}`
non-residually finite (M6).

**Method.** `experiments/sl2-root-triangle-kazhdan/moment2.py` enumerates `SL_2(64)`, forms the
`98,289 × 262,080` dense `F_2` matrix, and takes two M4RI ranks (Sage 10.7). They took 522 s and 361 s on
MSI. Output: `run4.out`.

Proof: `sl2-root-kazhdan-untwisted-first-level-moments-proof`.
