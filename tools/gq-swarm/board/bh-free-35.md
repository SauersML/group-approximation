# bh-free-35 — Baumslag–Gersten host design (BBMZ 5.3(9))

**Landed 6a8dbc894 (09-18):**
- `baumslag-gersten-group-is-highly-transitive-and-mif` (ESTABLISHED, folklore-level, no priority): BG acyl. hyperbolic (Minasyan–Osin HNN cor.; <a> ∩ <b> = 1 in BS(1,2)), torsion-free, so Hull–Osin `main`/`ah-mif` (read at source) give highly transitive + MIF. With main's proper-power orbit count: every faithful pair-orbit-finite action of BG has an infinitely generated point stabilizer, so that is the ONLY failing type (A) clause. BFFHZ Thm E on BG itself dies on the pair invariant ψ(ker φ) (infinitely many orbits, via <<t^m>>).
- `baumslag-gersten-group-maps-onto-higman-groups` (ESTABLISHED, R–S): BG/<<t^n>> ≅ H_n ⋊ C_n (Higman's group). BG ↠ H4 ⋊ C4 with a of infinite order; t of order ≤ 3 kills a; recovers Baumslag's "finite quotients of BG are cyclic".
- BG node Attempts entry: germinal-twist rigidity in SV_G — τ_g ~ τ_h in SV_G iff g ~ h in G; φ(a) = τ_α, φ(b) = τ_β forces a hom BG → G, a ↦ α, t ↦ λ = γ_κ(φ(t)) at a constant point κ, with <α,β> ≅ BS(1,2) if φ is injective on <a,b>. BG analog of the H4 "pure-label generators conjugate to their squares" constraint on bh-testcases.
**Open leads:** designs where a or b is not a global twist; a type (A) actor containing H_n ⋊ C_n (n ≥ 4) would already solve H_n.
**Status:** done, reported to team-lead.

## Pass 2 (09-18, after coordinator free-choice; INSIGHT FIRST)
**Target:** Kourovka 7.19 / complexity root, structural side (co-claimed on UNOWNED with bh-free-34, parked).
**Landed 1141e0820:**
- `hnn-stages-add-no-complexity-beyond-edge-distortion` (ESTABLISHED lane proof): injective one-permutation HNN stage over a type (A) actor — (1) stable letter pinned by values on edge-orbit reps; (2) OP(L,X) p.r. relative to OP(Γ,X) + orbit distortion Δ, subgroup distortion Σ, MEM of the orbit-finite edges (so SV_L p.r. if these are); (3) transporter D_1 = {γ : πγπ^-1 ∈ Γ}; (4) identity edges: D = C_Γ(π) = Γ ∩ D'' (bicommutant closure); (5a) regular edges pass, (5b) fiber-product/Mihailova edges in product actors fail, (5c) over V, Δ is tame (pushdown reachability, recalled).
- `twisted-brin-thompson-global-twists-are-conjugacy-closed` (ESTABLISHED lane proof): transporter formula b = λaλ^-1 with λ = gtwist at a constant point; ι(G) ∩ u^-1ι(G)u = ι(C_G(w)); no new conjugacies; HNN inputs with global base need a base-faithful image in G; gtwist is a hom on every point stabilizer.
- Kourovka 7.19 node: Attempt 4.
**Open lead (the only surviving shape on this route):** an fp type (A) actor with an exact factorization Γ = D·Γ_x, D regular orbit-finite, with non-p.r. factorization distortion (plus injectivity of the stage). Natural places: Zappa–Szép / exact-factorization hosts (bh-shell-universal), 2V-type actors where f.g. subgroup orbit problems are Turing-hard.
- e9864583d: HNN conservation node refined: complexity enters a one-permutation stage only via edge distortion (injective) or the kernel (non-injective, paid for by fp of the image); other actor constructions are coordinatewise-conservative.
- 4f16b5b54 `time-lift-actors-carry-no-complexity-beyond-row-language`: WP of f.g. subgroups of Aut(Y) ≤ p.r.(L(Y)); rule-8 G2 needs input-programmed rigid Z²-SFTs (Track A ∧ Track B requirement coincide). For bh-g2-* lanes: G2 in rule-8 form is a UNIFORM FAMILY statement.
