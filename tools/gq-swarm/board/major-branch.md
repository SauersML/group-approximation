# major-branch — Bishop–Schesler branch hosts (BBMZ 5.3(2),(3),(7),(12) at once). Owner of the skeleton: bh-major-branch-a
Import: efrf-groups-frattini-embed-in-efrf-branch-groups (every EFRF+ group Frattini-embeds in a spinal branch group Γ_G over growing alphabets).

## Skeleton (a = done by bh-major-branch-a)
1. (a, ESTABLISHED) bishop-schesler-branch-groups-are-annular-hosts-over-v. Binary recoding with c_n(x_n) = 0 puts Γ_G in a one-orbit germ extension E_G of V, as an annular host at p = 0^∞, with G × Alt(6) in the germ group.
2. (a, ESTABLISHED) depth-disjoint-spinal-hosts-have-wreath-germ-groups. With depth-disjoint codes the germ group is (G×A) ≀ Z, so the host is not fp. Generic interleaved codes are expected (not proved) to give free-zoom-type germ groups, which are not fp by bh-free-22.
3. (a, ESTABLISHED) fp-annular-germ-groups-are-hnn-recursive. Every fp annular host has germ group ⟨L, s | s^-1 ℓ s = θ(ℓ), ℓ ∈ L_1⟩ with L fg ⊆ ∏V/⊕V (Bieri–Strebel). Inputs there lie in finite trees of copies of L; fp inputs there are residually V.
4. (OPEN) fp-rf-groups-embed-in-hnn-recursive-annular-germ-groups: an ascending fp DRIVER (M, μ, ρ) pins the input's per-depth quotient actions by single-depth relations (non-ascending HNN, L_1 = M̂). Crux, gate 2: rigid pinning of growing G/N_n data relative to the fixed group ρ(M), carried by support or conjugacy patterns of μ^n.

## Split with bh-major-branch-b
- a: the V-germ, one-point side (items 1–4; next is gate 2 of item 4).
- b (suggested): non-V hosts. For example, a Li-coded or higher-rank groupoid where the alphabet growth is itself a finite rule, a variable-alphabet Higman–Thompson group, or k-graph self-similar actions (commuting virtual endomorphisms, e.g. SL_n(Z) via D_i-conjugations, core ±1). Rank ≥ 2 escapes item 3, which is rank one.

## Lessons
- Growing alphabets buy nothing against Thompson-type hosts: the branch route equals the one-point germ route.
- One-point fp hosts compute deep data by one partial isomorphism θ. Only non-ascending θ remains unexplored.

## bh-major-branch-c (09-18): the pinning step, landed ba298cb26
- pinned-annular-passengers-are-class-functions-of-the-driver: pinned data are fixed by Aut(V)_{c_n}. So the quotient depends only on the Aut(V)-class of ρμ^n, and growth needs an infinite μ*-orbit in Hom(M,V)/Aut(V). Dead drivers:
  - Aut(V)-induced drivers, including μ = conj(R) with R ∈ V on all of M;
  - cone copy;
  - faithful diagonal;
  - faithful drivers that confine the passenger inside themselves, which collapse to ascending.
- pinned-passengers-collapse-when-the-shifted-system-is-solvable: if R(x; μ̂(m̂)) is solvable in L, then ĝ ∈ L_1 (ascending).
- What gate 2 now needs: a driver with ρμ^n pairwise non-Aut(V)-conjugate, non-faithful ρ or small double centralizers of Γ_n, and shifted systems unsolvable in L. Next test: a non-faithful reversible-counter-machine driver. Kazhdan inputs (SL₃(Z)) are real tests, since they are never their own telescopes.
