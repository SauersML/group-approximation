# bh-kourovka-2146
Direction: Kourovka 21.46 (Fournier-Facio, "Well-known problem"): "Does there exist a finitely presented (infinite) simple group of finite cohomological dimension greater than 2?" (21tkt.tex l.13681).
Route under study: a torsion-free redesign of the Amir–Lazarovich lattices (AL Question 2, arXiv:2605.09493 l.2403), or a proof that the route cannot work.
- 15:30 started; nothing landed yet.
- 16:40 LANDED 40650f1e7:
  - commensurated-subgroups-of-virtually-simple-groups-are-rf (new);
  - kourovka-21-46-reduces-to-simple-amalgams-of-davis-lattices (new);
  - fp-simple-group-of-finite-cohomological-dimension-above-two (updated: constraints, the Davis–Neumann restatement, the sharpened parity condition, and the three-tree remark).
- Status: 21.46 is still OPEN. Established (lane proofs, unreviewed):
  - virtually simple groups have RF infinite-index commensurated subgroups;
  - so 3-tree import is dead and linear factors are excluded;
  - AL lattices are commensurability-rigid for torsion;
  - torsion-free T × X_{O_d} lattices with edge-transitive tree action are amalgams of Davis lattices of cd 3, with hyperplane sub-amalgams that are free.
- Next gate, EXT (relative Leighton for one hyperplane): extend a non-RF Burger–Mozes or Radu free amalgam F_a *_{F_e} F_b on H_0 ≅ T_d to commensurable Davis lattices W_1 ⊇ F_a, W_2 ⊇ F_b. Candidate tools: Woodhouse's Leighton proof for X_{O_d}, Haglund–Wise virtual retractions onto hyperplane subgroups, and AL's interlacing (which solves the involutive case).
- Sub-gate S: a one-vertex square complex with link O_d, for d = 12, 14 or 15 (a vertex-transitive torsion-free W). Existence is open, and the commutator design fails.
- Referee requests: gq-referee-a for the proof of the commensurated lemma and the amalgam reduction (items 2–4); gq-referee-b for the citations (AL l.113/897/2479, Radu l.2128, BM Props 3.3.1–3.3.2 in the biregular case).
- 17:xx LANDED ab6eeb0fd hyperplane-extensions-into-davis-lattices-are-split: EXT is proved. Coxeter-retraction section E: Aut(C) → Aut(X); Davis lattices K_0 ⋊ E(F) realize every free lattice F of T_d as a hyperplane stabilizer. The resulting Λ = K_0 ⋊ Γ is split, not just-infinite.
- Next gate, (IRR): a core-free realization of the hyperplane data. Try W_2 = φE(b)W_{F_a}E(b)^{-1}φ^{-1} with φ ∈ Comm(W_L), φ fixing C pointwise, commuting with E(F_e), and not preserving the fibres of r; then check (N1) density in U(Alt).
- LANDED cf4c856f6 twisted-davis-amalgams-keep-hyperplane-data. The twist lemma keeps Γ, stays torsion-free with cd 3, and leaves G_r. Wall twists are explicit. IRR ⇐ density. Density fails when the twist values fix D.
- Next: a finitely-many-orbits version of AL's local-to-global theorem, or vertex-transitivity of ⟨W_1, W_2⟩; the (N2) tree local action; and existence of a non-RF Γ with a colour-preserving edge group (or an E(F_e)-equivariant wall twist).
- LANDED 4afe513c6:
  - bm-lattices-have-color-preserving-edge-groups: inputs exist, at the cost of an index-2 subgroup; parity caveat for U(Alt).
  - al-local-to-global-holds-without-vertex-transitivity: AL's proof with the condition at all vertices gives closure ⊇ U^+, so density is a finite check. Credit AL.
- Next:
  - (DENS-fin) choose an explicit small wall twist ε (d = 6 or 8 with a Radu input) and produce 2-ball witnesses at the orbit representatives. This needs a bounded MSI computation; ask the coordinator first.
  - (N2) an all-vertex Burger–Mozes 3.5.3 for the biregular tree.
  - Parity: keep all local actions even.
- LANDED 7f25f45d8 tree-side-of-davis-amalgams-is-local-once-dense. (N1) implies the tree side is faithful and non-discrete; (N2) reduces to P_i ⊇ Alt(c_i). Explicit input: Γ_{6,6,k}^+ (Radu tables).
- The approved MSI job was deliberately NOT run: the input tables are unwired, the positive control is unwired, and one blind run would be poor signal. Next round: parse Radu's tables and code locally (no execution), then one job: (i) validate the datum, (ii) negative control on the split amalgam, (iii) the twisted certificate.
