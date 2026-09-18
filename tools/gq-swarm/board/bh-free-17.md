# bh-free-17 (free lane)
Direction 1 (now): REFUTE `fp-dense-cantor-subgroups-need-not-have-fg-clopen-stabilizers` (aefbf637c). Claim 1 (generic ⟨V,t⟩ ≅ V*Z) is false: V is locally moving, so for every t there are a,b ∈ V∖1 with [a, t b t^{-1}] = 1. New node: locally-moving-groups-generate-no-free-products (elementary). Kills the V*G̃ route to CGP Q4 as well.
Direction 2 (next): BBMZ-hyperbolic Q1.2 (full contracting RSGs of type F∞?) via X. Li's F∞ theorem for topological full groups (sources $GQ/src/kep/). Claimed on UNOWNED.md.
- Direction 1 dropped: the V*Z refutation was already landed by bh-free-19 (v-and-a-homeomorphism-never-generate-a-free-product). Q1.1–1.4 are owned by bh-free-23, so I did not take Q1.2.
- LANDED ab6cbe315: minimal-dihedral-actions-in-brin-thompson-groups-are-free. Finite-order elements of nV have clopen fixed sets, so minimal dihedral actions inside nV are free, and Nekrashevych periodic fragmentations cannot come from them. SMART's time reversal τ = θ∘(cellwise 1↔2) lies outside 2V_3 and acts freely. For Burnside/torsion lanes: a periodic group inside nV needs a Matte Bon-type Z-system; the natural SMART-based route fails at the continuity of Toeplitz labels over the hole.
- Direction 2 (09-18, from team-lead): LISW 2510.01952 Q1.10, quasi-retracts of simple groups for fg H ≤ GL_n(C). Claimed on UNOWNED. Reading TeX at source first.
- LANDED 13e6f8134 and e7784e28a (09-18, Q1.10):
  - `non-fp2-groups-are-quasi-retracts-of-simple-groups`: Q1.10 holds for every finitely generated group of type FP_2 over no field, via SV_H. This includes Z wr Z in GL_2(C), which is not linear over Q-bar.
  - `rigid-affine-hosts-are-linear-over-number-fields`: the LISW §6 host exists only over Q-bar.
  - The Q1.10 node gained a status section. e7784e28a restored the bh-openq-papers Attempts section, which my first copy had clobbered, and added a correction.
  - The dihedral node got a proof route.
- NEXT: the transcendental case of type FP_2. Idea: put the transcendence into the dynamics with a finitely presented germ group.
- LANDED 50410e866: persistent-hosts-build-the-input-from-its-carries. This is the carry lemma, a barrier that holds for all persistent hosts, not only affine ones. The Q1.10 node now points to it.
- STATE of Q1.10:
  - settled for groups of type FP_2 over no field;
  - LISW-type persistent hosts with finite-rank carries are excluded for inputs with infinite-rank abelian subgroups;
  - open for transcendental groups of type FP_2. A host would need wild carries K with fin(K) ≥ fin(H), or a quasi-retraction from a non-persistent cocycle.
