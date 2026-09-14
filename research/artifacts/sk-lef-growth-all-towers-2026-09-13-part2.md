# sk-lef-growth-all: cheap towers beyond Sturmian (part 2: one-hole Toeplitz subshifts)

Lane sk-lef-growth-all, 2026-09-13. Status: written proof, UNREVIEWED (queued with sk-referee-2).
Notation and Theorem C: part 1 and `research/artifacts/sk-lef-growth-bounds-2026-09-13-part2.md`.

## 5. One-hole Toeplitz subshifts
Let x ∈ A^Z be non-periodic, and for p ≥ 1 put Per_p(x) = {t : x_{t+jp} = x_t for all j}.

**Hypothesis (T).**
- 1 = p_0 | p_1 | p_2 | ⋯ with p_{k+1}/p_k ≤ ρ;
- for every k ≥ 1, the complement of Per_{p_k}(x) is a single residue class h_k + p_kZ;
- X is the orbit closure of x, and it is minimal (automatic for Toeplitz sequences).

Examples: the period-doubling sequence (p_k = 2^k) and the regular paperfolding sequence (p_k = 2^k).

**Theorem T1 (linear-cost towers).** Assume (T). For k ≥ 1 put `W_k = {y ∈ X : y_0 ≠ y_{p_k}}`. Then:
- W_k is nonempty and clopen;
- W_k ∩ T^tW_k = ∅ for 0 < |t| < p_k;
- |e_ij(e_{W_k})| ≤ |A|(5 + 48p_k).

*Proof.*
1. *Clopen, and cost.* W_k is the disjoint union over letters a of W(a,p_k) = {y_0 = a, y_{p_k} ≠ a}. So e_ij(e_{W_k}) is the product of the e_ij(e_{W(a,p_k)}). Apply part 1, Lemma 5.
2. *Nonempty.* If W_k = ∅, then T^s x ∉ W_k for all s, i.e. x_s = x_{s+p_k} for every s. So x is periodic, a contradiction.
3. *No short returns.* Suppose W_k ∩ T^tW_k ≠ ∅.
   - It is open and the orbit of x is dense, so it contains some T^s x. Then T^s x ∈ W_k and T^{s−t}x ∈ W_k.
   - That means x_s ≠ x_{s+p_k} and x_{s−t} ≠ x_{s−t+p_k}.
   - A position in Per_{p_k}(x) satisfies x_c = x_{c+p_k}. So s and s − t both lie outside Per_{p_k}(x), i.e. both are ≡ h_k mod p_k.
   - So t ≡ 0 mod p_k, and t = 0 or |t| ≥ p_k. ∎

**Theorem T2 (lower bound).** Assume (T). For every m ≥ 1 let k be least with p_k > 2m, so p_k ≤ 2ρm.
- W_k has no returns up to 2m, and κ ≤ |A|(5 + 96ρm).
- By Theorem C, L_X(r) ≥ 2^{18m²} for r ≥ 100|A| + (1920ρ|A| + 480)m.
- So `L_X(r) ≥ 2^{18((r − 100|A|)/(1920ρ|A| + 480) − 1)²}` for r ≥ 100|A| + 1920ρ|A| + 480, and L_X ≽ exp(r²). ∎

For period doubling, ρ = 2 and |A| = 2, so L_X(r) ≥ 2^{18((r − 200)/8160 − 1)²}.

## 6. Remarks
- The return argument uses only density of the orbit of x, not the odometer factor map. The same trick shortens part 1 step 3 for rotation codings.
- Several holes per period: W_k has returns only at differences of hole residues. Theorem T1 extends to hole sets whose pairwise cyclic differences are all > 2m, with the same cost.
- Examples outside (R) and (T): Thue–Morse (odometer factor, mixed spectrum) and Chacón (weakly mixing). They are tested numerically in part 3.
