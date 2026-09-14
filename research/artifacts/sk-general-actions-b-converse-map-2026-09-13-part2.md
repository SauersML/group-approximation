# When does a free minimal subshift give a LEF Kazhdan simple group? The converse side (part 2 of 2)

Lane `sk-general-actions-b` (SK swarm), 2026-09-13. Written proofs, UNREVIEWED. Part 1 has Lemma A, Theorem B, the group-level map, and the tower checklist.

## 6. Which Z^d subshifts qualify?

**Answer.** Let X ⊆ A^{Z^d} be a free minimal subshift. The following are equivalent:
- X has exact finite pattern models, i.e. finite Z^d-sets or partial models realizing exactly the windows of X;
- X is window-periodic;
- X is residually finite (Kerr–Nowak).

The equivalences come from Theorem B item 4, since Z^d is finitely presented, and `rf-subshifts-are-periodic-window-approximable`. For such X, EL_N(LC(X,F_q) ⋊ Z^d)/Z is infinite, finitely generated, simple, Kazhdan and LEF for every N ≥ 3 (`residually-finite-actions-give-matricial-crossed-products`, `steinberg-elementary-groups-are-simple-mod-centre`).

**Positive families.**
1. RF Toeplitz subshifts (`rf-toeplitz-subshifts-over-residually-finite-groups`).
2. Products X_1 × ⋯ × X_d of infinite minimal Z-subshifts, with Z^d acting coordinatewise.
   - They are minimal, since the orbit of a point is a product of dense orbits.
   - They are free.
   - Products of periodic words give the models.
3. Factors of window-periodic subshifts. Residual finiteness passes to factors without isolated points (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`, item 1).
4. **Proposition R below:** codings of free circle rotations by intervals with generic endpoints ("Sturmian Z^d configurations").

**Negative family.** No closed invariant subset of an SFT without periodic points qualifies, and no extension of one does (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`). Examples: Labbé's shift, and the minimal subsystems of the Robinson tilings. For these, LEF of EL_N is the quantum tiling question (`labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`).

**Contrast.** Labbé's shift is also a toral rotation coding (`labbe-shift-is-a-toral-rotation-coding`). What separates it from Proposition R is the geometry of the partition. A Markov partition has boundary points forced to coincide under the rotation, so rational perturbations change the cell structure. A generic partition has a stable cell structure, and rational perturbations give exact periodic models. **Whether a rotation coding qualifies depends on the partition, not on the rotation.**

## 7. Proposition R: generic rotation codings of Z^d are window-periodic

**Setting.**
- Let α = (α_1, …, α_d) ∈ R^d with 1, α_1, …, α_d linearly independent over Q. Put ⟨v, α⟩ = Σ v_i α_i and T = R/Z.
- Let m ≥ 2 and 0 = β_0 < β_1 < … < β_{m-1} < 1 with β_i − β_j ∉ Z + ⟨Z^d, α⟩ for i ≠ j.
- For t ∈ T let col(t) = i when t ∈ [β_i, β_{i+1}) (indices mod m), and x_t(v) = col(t + ⟨v, α⟩).
- Let X ⊆ {0, …, m−1}^{Z^d} be the closure of {x_t}. With (g·x)(h) = x(h − g), we have g·x_t = x_{t − ⟨g,α⟩}, so X is a subshift.

**Proposition R.** X is a free minimal subshift that is window-periodic, hence RF. So EL_N(LC(X,F_q) ⋊ Z^d)/Z is an infinite, finitely generated, simple, Kazhdan, LEF group for every N ≥ 3.

*Proof.*

**Cells.** Fix a finite W ⊆ Z^d and put P_W = {β_i − ⟨w, α⟩ mod 1 : i < m, w ∈ W}.
- The points of P_W are pairwise distinct. If β_i − ⟨w,α⟩ ≡ β_j − ⟨w',α⟩, genericity forces i = j, and then independence forces w = w'.
- So T∖P_W is a union of m|W| open arcs J.
- The W-pattern of x_t is constant on each arc, because x_t(w) changes only when t crosses β_i − ⟨w, α⟩. Call it p_J.
- Every point of X is a limit of codings x_t with t off the countable set of endpoints, so its W-pattern is some p_J. Every arc contains such t.
- So L_W(X) = {p_J : J an arc}.
- Let η > 0 be the least arc length, and C = max_{w ∈ W} Σ_i |w_i|.

**Freeness and minimality.**
- Coding generic points gives an almost one-to-one factor map X → T onto the minimal rotation (standard Sturmian argument: for t ≠ t', some v puts t + ⟨v,α⟩ and t' + ⟨v,α⟩ on opposite sides of β_1).
- The language is uniformly recurrent. Each arc J is an open interval, and the dense orbit t + ⟨Z^d, α⟩ enters J with bounded gaps by compactness of T and minimality of the rotation. So X is minimal.
- If v·x = x, the image point satisfies ⟨v, α⟩ ∈ Z, so v = 0. So X is free.

**Periodic models.**
1. Choose N > max(3/η, 3C/(2η)) and put a_i = round(Nα_i) and α' = a/N. Then |α_i − α'_i| ≤ 1/(2N), so |⟨w,α⟩ − ⟨w,α'⟩| ≤ C/(2N) < η/3 for w ∈ W.
2. Put P'_W = {β_i − ⟨w, α'⟩}. Each point moves by less than η/3, so P'_W has the same cyclic order as P_W.
   - Its arcs J' correspond to the arcs J and have length > η/3 > 1/N.
   - The pattern of a point of J' computed with α' is p_J, since it is determined by the cyclic position of t among the points of P'_W.
3. Let T_N = t_0 + (1/N)Z/Z, where t_0 avoids the finite set P'_W + (1/N)Z. Z^d acts on T_N by t ↦ t + ⟨v, α'⟩.
   - Every arc J' contains a point of T_N, because its length exceeds 1/N.
   - No point of T_N lies on P'_W.
4. For t ∈ T_N put y_t(v) = col(t + ⟨v, α'⟩). Then y_t is NZ^d-periodic, and g·y_t = y_{t − ⟨g,α'⟩}, so O = {y_t : t ∈ T_N} is finite and invariant.
5. Every translate satisfies (g^{-1}·y_t)|_W = y_{t + ⟨g,α'⟩}|_W = p_{J'} ∈ L_W(X). So O ⊆ X_W, and O realizes every p_J.
6. So X is window-periodic, and RF by `rf-subshifts-are-periodic-window-approximable` (X is perfect, being infinite and minimal).
7. The group-theoretic conclusion follows from `residually-finite-actions-give-matricial-crossed-products` and `steinberg-elementary-groups-are-simple-mod-centre`. ∎

**Remarks.**
- For d = 1 this recovers the Sturmian case, which the note's return-word argument already covers.
- The same proof works for codings of Z^d-rotations on higher-dimensional tori by polytopes, provided the cell structure at every window is stable under small perturbations of α.
- Credit: two-dimensional Sturmian configurations are due to Berthé–Vuillon (Discrete Math. 223 (2000), "Tilings and rotations on the torus: a two-dimensional generalization of Sturmian sequences"; recalled, not reread). No novelty is claimed for the periodic approximation; the literature check is bounded (none beyond memory).

**Model test.**
- Endpoints in special position, e.g. β_1 − β_0 = α_1 with d ≥ 2 and suitable windows, can create coincident points of P_W. The genericity hypothesis excludes this.
- Labbé's partition is not generic in the corresponding polygon sense and is not window-periodic, as it should be.
