# sk-lef-growth-all: cheap towers beyond Sturmian (part 4: the Chacón subshift)

Lane sk-lef-growth-all, 2026-09-13. Status: written proof, UNREVIEWED (queued with sk-verify-7).
Notation and Theorem C: part 1 and `research/artifacts/sk-lef-growth-bounds-2026-09-13-part2.md`.

## 10. Setting
- B_0 = 0 and B_{n+1} = B_n B_n 1 B_n, so h_n = |B_n| satisfies h_0 = 1 and h_{n+1} = 3h_n + 1 (1, 4, 13, 40, 121, 364, …).
- X_Ch is the orbit closure of the one-sided limit x = lim B_n (the fixed point of 0 ↦ 0010, 1 ↦ 1).
- B_n begins and ends with 0.
- Chacón's system is weakly mixing, so it has no eigenvalues. This is recalled and not used; it explains why parts 1–3 do not apply.

**Level-n decomposition.**
- For M > n, B_M is a concatenation of copies of B_n. Between consecutive copies there is a slot holding either nothing (0) or one letter 1 (1).
- B_{n+1} = B_n [0] B_n [1] B_n, and B_M is a concatenation of B_{n+1}-copies with level-(n+1) slots between them.
- So the level-n slot sequence reads 0, 1, s_1, 0, 1, s_2, … with s_i the level-(n+1) slots.

**Lemma Ch0.** In B_M, consecutive level-n slots equal to (0, 1) occur exactly at the first two slots inside each B_{n+1}-copy.

*Proof.* The consecutive pairs are (0,1), (1,s_i) and (s_i,0). Only the first can be (0,1). ∎

**Lemma Ch1 (linear recurrence).** Every word of X_Ch of length R ≥ 18n + 9 contains every word of X_Ch of length n. Consequences:
- X_Ch is minimal;
- it is infinite, by Theorem Ch below (occurrences of W_n have gaps ≥ h_{n+1}, which is unbounded);
- by sk-lef-growth Theorem A(c), N(n) ≤ 36n + 18 and L_{X_Ch}(r) < 2^{9(144r+54)²}.

*Proof.* Let h_{k−1} < n ≤ h_k.
- A window of length n in x meets at most two consecutive level-k copies and the slot between them, so it lies in B_k B_k or B_k 1 B_k. Both occur in B_{k+1}.
- Every window of length 2h_{k+1} + 1 contains a full B_{k+1}-copy.
- h_{k+1} = 9h_{k−1} + 4 < 9n + 4. ∎

## 11. Linear-cost towers
**Theorem Ch.** For n ≥ 1 put `W_n = {y ∈ X_Ch : y_0 = 0, y_1 = 0, y_{h_n+1} = 1}`. Then:
- W_n is nonempty and clopen;
- W_n ∩ T^tW_n = ∅ for 0 < |t| < h_{n+1};
- |e_ij(e_{W_n})| ≤ 154 + 48h_n.

*Proof.*
1. *Local characterization.* Let c be a position of B_M with c + h_n + 1 < |B_M|. We claim B_M[c] = B_M[c+1] = 0 and B_M[c + h_n + 1] = 1 exactly when c is the last position of a level-n copy followed by the slot pair (0, 1).
   - Since B_M[c] = 0, the position c is not a spacer. Let c lie in a copy at offset o, and let σ be the slot after that copy.
   - *o ≤ h_n − 2.* Position c + h_n + 1 sits at offset o + 1 − σ ∈ [0, h_n − 1] of the next copy. So B_M[c+h_n+1] = B_n[o+1−σ]. That equals B_M[c+1] = 0 when σ = 0, or B_M[c] = 0 when σ = 1. So it is not 1.
   - *o = h_n − 1.* B_M[c+1] = 0 forces σ = 0, so c + 1 starts the next copy. Position c + h_n + 1 is the letter right after that copy: 1 if the next slot is 1, and the first letter 0 of a copy otherwise.
2. *Nonempty.* In any B_{n+1}-copy, c = h_n − 1 (offset inside the copy) satisfies the characterization, and c + h_n + 1 = 2h_n is the spacer inside the copy. Every word of X_Ch lies in some B_M, and W_n is a finite Boolean combination of cylinders.
3. *No short returns.* Let y ∈ W_n ∩ T^tW_n with 0 < t < h_{n+1}. The case t < 0 is the same with (T^{-t}y, −t).
   - Then y_c = y_{c+1} = 0 and y_{c+h_n+1} = 1 for c ∈ {0, −t}.
   - The word y_{[−t, h_n+1]} occurs in the middle copy of some B_{M+1} = B_M B_M 1 B_M, so all positions used lie inside B_{M+1} with room on both sides.
   - By step 1 both occurrences are ends of first copies of B_{n+1}-copies (Lemma Ch0), at the same offset h_n − 1 inside distinct B_{n+1}-copies.
   - Distinct B_{n+1}-copies start at least h_{n+1} apart, so t ≥ h_{n+1}, a contradiction.
4. *Cost.*
   - e_{W_n} = e_0 · (u^{-1}e_0u) · (u^{-(h_n+1)}e_1u^{h_n+1}).
   - With k the third index, e_ik(e_0 · u^{-1}e_0u) = [e_ij(e_0), e_jk(u^{-1}e_0u)] has length ≤ 2 + 2(1 + 24) = 52 by Lemma 1.
   - e_ij(e_{W_n}) = [e_ik(e_0u^{-1}e_0u), e_kj(u^{-(h_n+1)}e_1u^{h_n+1})], of length ≤ 104 + 2(1 + 24(h_n+1)) = 154 + 48h_n. ∎

**Corollary Ch2.** L_{X_Ch} ≃ exp(r²). Precisely:
- `L(r) ≥ 2^{18((r − 3080)/2400 − 1)²}` for r ≥ 7880;
- `L(r) < 2^{9(144r+54)²}` for all r.

*Proof.*
- For m ≥ 2 let n be least with h_{n+1} > 2m. Then n ≥ 1 and h_n ≤ 2m (for n = 1 because h_1 = 4 ≤ 2m).
- Theorem Ch gives no returns up to 2m and κ ≤ 154 + 96m.
- Theorem C gives L(r) ≥ 2^{18m²} for r ≥ 3080 + 2400m. Take m = ⌊(r − 3080)/2400⌋ ≥ 2.
- The upper bound is Lemma Ch1. ∎

## 12. Numerics (MSI, `towers.py` and `towers2.py` in the lane dir; evidence only)
- Search over all 2- and 3-letter patterns of span ≤ 130 on 2^18 letters of the Chacón point, keeping patterns with at least 3 occurrences. The least-span pattern with minimal gap > 2m is exactly {0 ↦ 0, 1 ↦ 0, h_n + 1 ↦ 1}, with minimal gap h_{n+1} (13, 40, 121, 364), for m = 4 … 128.
- Thue–Morse: the mismatch set of the derivative at shift 2^k has minimal gap exactly 2^k for k = 1 … 8, matching Lemma TM1 and Theorem T1.
- Tribonacci: 2- and 3-letter patterns of span ≤ 58 separate returns up to 256. No proof here: the Tribonacci factor is a 2-torus rotation with a fractal partition.

## 13. Status of the general question
- Proved, unreviewed:
  - exp(Θ(r²)) for Sturmian (sk-lef-growth), Thue–Morse, period doubling and Chacón;
  - the lower bound for every extension of a rotation coding with an arc letter, or of a one-hole Toeplitz subshift with bounded ratios;
  - the upper bound whenever special factors are bounded.
- Mechanism: in every case a letter-change test at a partial-rigidity time (q_n, p_k, h_n) isolates one position per level-(n+1) block.
- Open:
  - linearly recurrent subshifts without such a test, e.g. primitive substitutions with several level blocks or non-constant heights;
  - zero-entropy minimal subshifts that are topologically mixing (substitution subshifts never are, by Dekking–Keane; recalled).

  There, k-letter patterns may need k → ∞, and the cost of a product of k letters with shifts ≤ s is O(k²s). That still gives exp(cr²/polylog r) if k = O(log m) suffices.
