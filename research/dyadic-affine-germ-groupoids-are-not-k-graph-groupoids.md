---
rg: 2
id: dyadic-affine-germ-groupoids-are-not-k-graph-groupoids
kind: claim
title: For a finite k-graph, H_0 of the path groupoid vanishing at a prime l forces all its homology to vanish at l; the germ groupoid of Aff(Z[1/2m], U) on Z_2 fails this at l = 2, so V_2(BS(1,r)) for odd |r| >= 3, including BS(1,3), is the full group of no finite k-graph, for any k
distinct_from:
  basilica-rn-group-is-not-a-k-graph-full-group: that uses rational homology and a section character; BS(1,3) passes that test (its germ groupoid is rationally acyclic), and this integral, prime-by-prime test excludes it.
  s-arithmetic-affine-rn-groups-are-k-graph-full-groups: that builds k-graph models over F_q(t); this shows that the analogous groupoids over Q at the place 2 never have one, and it machine-checks the BS(1,3) homology sketched there.
  torsion-germ-rn-groups-are-not-k-graph-full-groups: that excludes torsion or non-Hausdorff germs; the groupoids here are Hausdorff with torsion-free multipliers.
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/dyadic_affine_homology.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-dyadic-affine-homology.txt
---

**ESTABLISHED (proof in `dyadic-affine-germ-groupoids-are-not-k-graph-groupoids-proof`; lane proof, w13-101; not
independently reviewed).** Imported: the Farsi–Kumjian–Pask–Sims Koszul formula for `k`-graph groupoid homology
(arXiv:1808.07807), Atiyah–Macdonald Cor. 2.5 (Nakayama), the Lyndon–Hochschild–Serre spectral sequence, and part 1
(rigidity) of `basilica-rn-group-is-not-a-k-graph-full-group`. The rest is proved in full.

## Statement

**1. Prime-support theorem.** Let `Λ` be a finite `k`-graph with no sources (any `k ≥ 1`), and let `ℓ` be a prime
or `ℓ = 0` (with `Z_(0) = Q`). If `H_0(G_Λ) ⊗ Z_(ℓ) = 0`, then `H_n(G_Λ) ⊗ Z_(ℓ) = 0` for every `n`.
- In particular, `H_0(G_Λ) = 0` forces `H_*(G_Λ) = 0` integrally.
- Every prime in the torsion of some `H_n(G_Λ)` divides the order of `H_0(G_Λ)`, when `H_0` is finite.
- The same holds for every ample groupoid Kakutani equivalent to `G_Λ`, since homology is a Morita invariant.
- For `ℓ = 0` this recovers part 2 of `basilica-rn-group-is-not-a-k-graph-full-group` in one line.

**2. Dyadic affine groupoids.** Let `m ≥ 1` be odd and let `U ≤ Z[1/2m]^×` be torsion-free with `v_2(U) = gZ`,
`g ≥ 1`. Let `𝒢 = 𝒢_{m,U}` be the groupoid of germs of `x ↦ ux + b` (`u ∈ U`, `b ∈ Z[1/2m]`) at points `ω ∈ Z_2`
with `uω + b ∈ Z_2`. For `u ∈ U`, write `u' = u·2^{-v_2(u)}` for its odd part. Then:
- `H_0(𝒢) = Z/(2^g - 1)`, which has odd order;
- `H_1(𝒢) ⊗ Z_(2) ≅ Z_(2)/(u' - 1 : u ∈ U) ≠ 0`, because every `u' - 1` is even.

So by part 1, `𝒢` is not Kakutani equivalent to the path groupoid of any finite `k`-graph with no sources, for any
`k ≥ 1`.

**3. Baumslag–Solitar groups.** Let `r` be odd with `|r| ≥ 3`. Let `BS(1,r) = ⟨x + 1, rx⟩` act on `Z_2`, which is
the binary tree. This action is faithful and self-similar.
- The germ groupoid of `V_2(BS(1,r))` is `𝒢_{|r|,⟨2,r⟩}`.
- Its homology is `H_0 = 0`, `H_1 = H_2 = Z/|r-1|`, and `H_{≥3} = 0`. It is rationally acyclic.
- So `V_2(BS(1,r))` is **not** `F(G_Λ)` for any finite `k`-graph `Λ` with hypothesis (H), for any `k ≥ 1`.
- **`r = 3` is the case left open by w12-101.** The germ groupoid of `Aff(Z[1/6], ⟨2, 3⟩)` on `Z_2` has
  `H_0 = 0` and `H_1 = H_2 = Z/2`, as sketched there, and is the path groupoid of no finite `k`-graph, `k ≥ 2`
  included.
- More generally this holds for `V_2(Z[1/m] ⋊ U')`, for any odd `m` and any torsion-free `U' ≤ Z[1/m]^×`.

**4. Odd places.** Let `p` be an odd prime and `m` a positive integer prime to `p`. Let `U ≤ Z[1/pm]^×` be
torsion-free with `v_p(U) = gZ`, `g ≥ 1`. The same computation gives:
- `H_0 = Z/(p^g - 1)`;
- `H_1 ⊗ Z_(ℓ) ≅ Z_(ℓ)/(u' - 1 : u ∈ U)` for every prime `ℓ ∤ m(p^g - 1)`, where `u'` is the prime-to-`p` part
  of `u`.

So `𝒢` has no finite `k`-graph model as soon as one of these holds:
- some prime `ℓ ∤ m(p^g - 1)` divides every `u' - 1` (`ℓ = p` is allowed);
- every `u'` equals `1`.

Examples:
- **Excluded:** `V_3(BS(1,7))` at `ℓ = 3`, and `V_5(BS(1,7))` at `ℓ = 3`.
- **Not excluded:** `V_3(BS(1,2))`, i.e. `Aff(Z[1/6], ⟨2, 3⟩)` on `Z_3`. Its homology `(Z/2, Z/2, 0)` is that of the
  one-vertex 2-graph with `(3, 3)` loops.

## Machine check (`dyadic_affine_homology.py`)

- **A.** An independent Pimsner–Voiculescu route to part 3. The transfer and conjugation matrices on
  `H_1(2^m Z[1/r] ⋊ ⟨r⟩)` are computed by coset enumeration, for 12 values of `r` and `m ≤ 6`.
  - They come out as `[[2,0],[(r-1)/2,1]]` and the identity.
  - This gives `H_0 = 0` and `H_1 = H_2 = Z/|r-1|`.
- **B.** The Lyndon–Hochschild–Serre and Koszul computation of part 2, for 12 choices of `(m, U)`, agrees with A.
- **C.** Part 1 is checked on 2,500 random commuting tuples (`k ≤ 3`, `|Λ^0| ≤ 3`), 1,425 of them with `H_0 = 0`,
  and on all 743 commuting pairs of `2×2` matrices with entries in `{0,1,2}`.
  - There are no violations.
  - No pair has the homology `(0, Z/2, Z/2)` of the BS(1,3) groupoid.
- **D, E.** Germ decomposition (the Lemma D analogue), for `p = 2` and for odd `p`: 681 random cases.

## What this decides

- **The step is decided negatively, for every `k`.** The `k`-graph route to `F_∞` for `V_2(BS(1,r))` is closed.
  No choice of `k`, of vertex set, or of Kakutani-equivalent model can help.
- **Dichotomy over global fields at the place 2.**
  - Over `F_q(t)`, every `S`-arithmetic affine germ groupoid with torsion-free units is a one-vertex `k`-graph
    groupoid (`s-arithmetic-affine-rn-groups-are-k-graph-full-groups`).
  - Over `Q` at `v = 2`, none is, and the obstruction is purely 2-primary.
- **What remains open.** The first case that passes every known homological test is `V_3(BS(1,2))`: `Aff(Z[1/6], ⟨2, 3⟩)`
  acting on `Z_3`. Decide whether it is a 2-graph groupoid.
