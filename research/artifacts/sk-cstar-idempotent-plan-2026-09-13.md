# sk-cstar-idempotent: plan (2026-09-13, wave 11)

Lane sk-cstar-idempotent. Problem: is `G_X = EL_3(LC(X,F_2) ⋊_T Z)` C*-simple? Open node: `subshift-elementary-groups-are-cstar-simple` (Attempts 1–7).

## State on main (read, not re-derived)
- **Criterion** (`cstar-simple-iff-amenable-subgroups-not-confined`): C*-simple iff no nontrivial amenable subgroup is confined.
- **Import** (`confined-subgroup-commutator-lemma`): Le Boudec–Matte Bon Theorem 3.17 for permutation groups. It needs a displacement configuration `{Ω_σ}` for the confining set `P` and rigid stabilizers whose nontrivial conjugacy classes have more than `|P|` elements.
- **Tested subgroups:** root subgroups, `GL_n(LC)`, the images of `[[T]]'` and `[[T]]`, and the cut stabilizers `S_y` are not confined (sk-cstar-simple, sk-verify-7/13 PASS).
- **Dead routes:**
  - BKKO normalish: `S_y` is locally finite and normalish;
  - (CS);
  - countably many amenable subgroups;
  - per-element averaging, which only gives unique trace;
  - linear permutation actions: rigid stabilizers of proper vector sets are trivial.

## Choice
Transfer the commutator lemma from sets to idempotents of `M = M_3(R)`, then build idempotent displacement configurations for every finite `P ⊂ G ∖ {1}`.

**(A) Ring commutator lemma.** Dictionary:
- support `Ω` ↔ nonzero idempotent `E ∈ M`;
- `Ω ∩ Ω' = ∅` ↔ `EE' = E'E = 0`;
- `σ(Ω)` ↔ `σEσ^{-1}`;
- "`σ` fixes `Ω` pointwise" ↔ `σE = Eσ = E`;
- rigid stabilizer ↔ a subgroup `R(E) ≤ G ∩ (I + EME)`.

Only two facts about rigid stabilizers enter the commutator calculus:
- `R(E)` and `R(E')` commute when `E ⊥ E'`;
- `σR(E)σ^{-1} ≤ I + (σEσ^{-1})M(σEσ^{-1})`.

Both hold for any subgroup of `I + EME`. The work is to re-read LBMB's proof (arXiv:2006.08677 §3, restated in arXiv:2012.03997 §3) and check that every step uses only these facts plus pairwise orthogonality.

**(B) Existence of configurations.**
- Fibrewise transvections move no clopen set, yet they displace rank-one idempotents. Over `F_2`, `σ = e_12(1)` and `E = [[1,0],[1,0]]` give `σEσ^{-1} = [[0,0],[1,1]] ⊥ E`.
- The corner of `E = e_V·(rank-one idempotent)`, with `V` a tower base of height `≥ 3`, contains `EL_3` of a first-return crossed product. That group is infinite, finitely generated, simple and Kazhdan (Theorem 2), so its nontrivial conjugacy classes are infinite and it has no proper finite-index subgroups.
- Obstruction to handle: condition (iii) fails for every involution (`σ^{-1}Eσ = σEσ^{-1}`), and all transvections are involutions in characteristic 2. Check at source how LBMB treat `σ^2 = 1`: replace `P`, pass to products, or use a weaker configuration.

**(C) Conclusion.** A confined `H` contains a nontrivial `N ≤ R(E_ρ)` whose normalizer in `R(E_ρ)` has index `≤ r`. With `R(E_ρ) = EL_3(corner)` infinite simple, that normalizer is everything, so `N` is normal and equals `R(E_ρ)`. So `H` is non-amenable, and `G_X` is C*-simple.

**Fallback (D).** Uniform conjugate ping-pong: for each finite `P`, find `g_1, g_2` with `⟨g_1^{-1}p_1g_1, g_2^{-1}p_2g_2⟩` non-amenable for all `p_i ∈ P`.

**Deliverable.** Either the theorem with a complete proof (queued with sk-verify-13), or an exact obstruction on the open node.
