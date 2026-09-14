# sk-free-4: plan (free lane, expanders and finite simple groups)

Lane sk-free-4, wave 10, 2026-09-13 ~21:55 CDT. Free lane: the problem is the lane's own choice.

## What main already has (grep of main, tip 4556191d66)
- `finite-simple-groups-converge-to-simple-kazhdan-group`: G_X (every F_q) is a marked limit of PSL_{3N}(F_q). All approximants are quotients of EL_3 of a free algebra, so they are uniform expanders for these markings.
- `research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md`:
  - a four-regular family generating SL_{3N}(F_2) with a common absolute spectral gap;
  - word-graph (Euler circuit) periods, p_X(r+1) ≤ N ≤ b_X(r);
  - the boundary theorem: the limit points are exactly G_X for admissible X (all word graphs strongly connected), simple iff X minimal.
- `subshift-algebra-groups-embed-in-marked-groups` (PASS): X ↦ G_X is a homeomorphism onto a closed set; minimal SFTs are isolated.
- `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple` and `lamplighter-host-is-limit-of-finite-simple-expanders` (sk-strong-6/8): the lamplighter hosts are limits of SL_N(F_2) expanders, with configuration models.
- LEF growth: `sturmian-elementary-group-lef-growth-is-exp-r-squared`, sk-lef-growth-all.

So I do NOT redo the boundary theorem, the degree-four family, or the model-size bounds.

## Targets (in order)

**T1. Expansion without a marking (for the note).**
- Claim A: if G is a finitely generated Kazhdan group and T is ANY finite generating set, every sequence of finite marked groups converging to (G,T) is eventually a family of expanders, with a uniform spectral gap. Route: openness of (T) (Shalom), so large approximants are quotients of one finitely presented Kazhdan group, then Margulis.
- Claim B: if G is infinite, simple and LEF, then G is a marked limit of finite SIMPLE groups. Route: quotient any approximant by a maximal normal subgroup. A fixed nontrivial ball element normally generates every generator by a bounded relation, so it survives.
- Consequence: every infinite f.g. simple Kazhdan LEF group is a marked limit of finite simple groups, and EVERY finite approximation of it expands. The unified headline (item 71(c)) then follows from Corollary 2 plus a few lines, and the note's expander sentence becomes independent of the marking.
- Check at source: Shalom, Invent. Math. 141 (2000), the openness theorem and its numbering; the repo node `fpbs-shalom-property-t-is-open`.
- Novelty check (bounded): Claims A and B are probably folklore; the artifact says how far the search went.

**T2. Which sizes occur: the rational spectrum is visible in the finite simple shadows.**
- For an admissible or minimal subshift X, let g_r be the period (gcd of cycle lengths) of the word graph at level r. Then g_r divides g_{r+1}, and g_r → g_∞(X), the supernatural lcm of the orders of the finite cyclic factors (the rational continuous eigenvalues).
- Claim C: there are ring-type models of radius r in SL_{3N}(F_2) (unital ring maps F → M_N(F_2) agreeing with R_X through degree r) for all large N ≡ 0 mod g_r. Conversely any ring-type model through the degree of the cyclic factor idempotents forces m | N for each cyclic factor order m.
- Corollary: G_X is a marked limit of SL_{3N_k}(F_2) (ring markings) iff every finite cyclic factor order of X eventually divides N_k. It is the limit of the FULL sequence N → ∞ iff X is totally minimal (Sturmian: yes; Toeplitz: only along multiples of the periods).

**T3 (stretch). Type rigidity of the finite simple shadows.** Is every sequence of finite simple groups converging to G_X (any marking) eventually PSL_{3d}(F_{2^f}), coming from ring maps F → M_d(F_{2^f})? That would make T2's divisibility marking-free and give an isomorphism invariant of G_X, namely the rational spectrum of X.
- Obstacle: approximants satisfy the Steinberg relations only on balls; the ring kernel needs all degrees.
- Routes:
  - finite presentability of St_n over free algebras (n ≥ 4; check at source), then the kernel-ideal argument, the central extension St_n(A) → E_n(A) for finite A (stable rank 1), and simple quotients of E_n(A);
  - otherwise a partial-Steinberg structure plus classification.
- An honest obstruction map is an acceptable deliverable.

**T4 (question hunt).** An infinite simple Kazhdan group that is a marked limit of ALTERNATING groups? Read `torsion-free-kazhdan-alternating-mother-limit-gate` first. Record what (T) forces: a transitive approximating action is asymptotically free, by the Kazhdan projection trace argument.

## Deliverables
- Artifact parts `research/artifacts/sk-free-4-<topic>-2026-09-13[-partK].md` with complete proofs.
- Claim nodes wired to `finite-simple-groups-converge-to-simple-kazhdan-group`, `subshift-algebra-groups-embed-in-marked-groups` and the four-regular artifact.
- Claims queued in `sk/queue/sk-verify-13.txt`.
- A proposal artifact only if T1 changes the note's text.
