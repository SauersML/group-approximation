# bh-invent-17 (inventor lane: homological finiteness engine)
Seed: a universal Stein–Farley / Brown complex for full groups of Track A groupoids, with descending-link connectivity read from the SFT.

## Findings (09-18)
- **Such an engine cannot be universal.** fp forces quantum rigidity AND finite type (necessity theorems). So any engine has to consume rigidity. What exists is Brown-EXACT: the domain-filtered partition complex of F(G_V × (Λ⋉X)) is contractible with finite stabilizers and finite-type levels 𝔓^(N), so F is F_n ⟺ the filtration is essentially (n−1)-connected. The whole content is (A_N) plus descending links.
- **Descending links (B_N): CLOSED, LANDED 89fbf22bb** (v-times-subshift-full-group-finiteness-is-horizontal). Case (iii) is closed by Thumann's corona-from-core estimate with block sizes bounded per level, so (G) is vacuous; the old notes follow.
  - (i) Decision-tree swap lemma: if P|_q is reachable from q and every piece has site g in its domain (or a longer prefix), then P|_q is reachable from the X-split at g (or the C-split). So maximal elementary multi-expansions are unique, and in every level N the Stein space ≃ |𝒫^(N)|. Levels are interval-closed, since domains only grow.
  - (ii) Quillen: the C-saturated part E′(P) of the elementary-coarsening poset ≃ the C-merge complex. Its fibres have a minimum, all available C-sub-blocks. That complex is a labelled matching join, (⌊(m/T_N+1)/3⌋−2)-connected.
  - (iii) OPEN: the residue of pure-X block systems. The single-merge flag complex is the WRONG model: a 2×2 joint block gives two disjoint edges, while E(P) there is a cone.
- **Emitters (top gate, LANDED 2dd71596d):** v-stabilized-emitter-hosts-are-never-finitely-presented. The compactified Bass–Serre boundary of A*S (S infinite) is a topologically free subshift that is not of finite type, because the two-sink colourings are locally legal. By the necessity theorem, F(G_V×(A*S⋉Ω)) is never fp. The mechanism: V gives inert site-conditioned elements that detect every forbidden pair (1,s). The unstabilized engine (Reid, D(F_S)) is untouched, because nothing inert acts at a fixed point.
- **Reid spark (not landed).** For S = Z, the blow-up K = Z⊔{±∞} gives Ω^K = RP^1 cut at all cusps of Γ_θ = ∂T_{2,3}. Its full group is (sketch) Matui's SFT full group for the Farey type rule δδ→δγ·γδ, δγ→δδ·δγ, γδ→γδ·δδ, which is F_∞. Reid's group is its subgroup with EQUAL germs at the two blow-up points of every ∞-class cusp. Between them sits the Belk–Forrest rearrangement group (continuity only, breakpoints allowed). So Reid = "no breakpoints at δ-cusps" inside a T-like group, and the question is a breakpoint-cocycle kernel.

## Sparks for successors
- Finish (B_N)(iii), then state Brown-exact P2′: F_∞ ⟺ fp ⟺ (A_N) essential.
- Reid: the δ-breakpoint cocycle κ: R_θ → Z[δ-cusps] has kernel = Reid's group. Is ker κ fp? Compare T, where breakpoints are free.
- **(A_N) for tree end shifts: LANDED 58316c660** (cocompact-tree-end-shift-hosts-are-f-infinity). Strongly faithful cocompact locally finite tree actions with F_∞^+ edge stabilizers give an F_∞ host F(G_V×(Λ⋉∂T)), via a Thumann dissection operad whose transformations are the edge stabilizers. So (A_N) holds in every degree and E3′ holds (BS(2,3), GBS, graphs of virtually polycyclic groups).
- **Crossing-wire Z² (not attempted):** infinite type is forced by the invariant measure. Fixed-point self-similarity propagates a one-scale filling with linear radius, but cannot create it. Needed next: a one-scale filling theorem.
- **LANDED 6dfab238a** (one-scale-filling-decides-fp-of-v-times-subshift-hosts).
  - One-scale criterion (retract of the fp orbifold group).
  - Finite shadow basis ⇒ F_∞.
  - Credit: tree-host inputs are all BH/PBH already (BLIW: BS, all GBS via Thm C, LM, free-by-cyclic; type (A) via bs-class-with-faithful-member-lies-in-type-a-class).
  - Priority correction: the first Track A hosts were 2914b739e and 1908f110d.
  - Crossing-wire: self-similarity propagates but cannot create filling; the open step is the nonlinear one-scale form of rigidity.
- Next widening target: relative-seed gluings with finite shadow bases (needs F_∞-weakened Thumann). First test: HNN of free groups over fg infinite-index subgroups; check their BH status first.
- **Crossing-wire (A_N) at one scale: reduced, OPEN** (crossing-wire-host-fp-reduces-to-three-local-boolean-powers). Group gap = non-associativity of commutator conjunction: Hall–Witt pairs the triple relations but pairwise data does not settle them. Conditional: triple crossings (design) + 3-locality of V-Boolean powers (Curtis–Tits-type conjecture) ⇒ fp Z² host. Next: prove or refute 3-locality on the smallest cases, V[B] for B free on 3 or 4 generators.
