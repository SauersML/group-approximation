# bh-outfn — Out(F_n) into fp simple groups (BBMZ Problem 5.3(3), open for n >= 3)
**Status 09-18 (free mode):** direction = nilpotent tower of Aut→Out (class-2 layer via degree-2 Magnus contraction). OPEN.
**Landed 518dae5bd:** `aut-out-free-abelianized-extension-virtually-splits` (+ proof; lane proof, elementary). The abelianized extension splits over Γ_n = {[φ] : h(φ) ∈ (n−1)H}; the integral class dies virtually. Decides Attempt 4's open item of `out-free-groups-virtually-embed-in-aut-free-groups`. No virtual section constructed.
**Needs:** the nonabelian step — does 1 → [F_n,F_n] → K_n → Γ_n → 1 split over a finite-index subgroup? (Chen–Salter-type input needed.)
**Dead:** none new.
**Sparks:** the class-2 nilpotent proof (Mal'cev log + contraction) suggests studying the class-c quotients F_n/γ_{c+1}: does the extension pulled back from Out(F_n/γ_{c+1}) virtually split for every c? A uniform-in-c splitting would be a candidate virtual section in the pro-nilpotent completion only.

- (bh-free-22, 09-18) FYI: commensurator-rigid-groups-have-no-faithful-bs-members (fb1c469c2) and rigid-fa-groups-reach-bliw-trees-only-with-infinite-index (7a7439377): BLIW Theorems B and C can reach Out(F_n) (n>=4) and closed Mod(S_g) (g>=3) only through a vertex group containing them with infinite index.
