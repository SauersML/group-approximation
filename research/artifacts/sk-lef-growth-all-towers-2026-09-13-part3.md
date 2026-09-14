# sk-lef-growth-all: cheap towers beyond Sturmian (part 3: factor monotonicity and Thue–Morse)

Lane sk-lef-growth-all, 2026-09-13. Status: written proofs, UNREVIEWED (queued with sk-verify-7).
Notation: part 1, and `research/artifacts/sk-lef-growth-bounds-2026-09-13-part1.md`.

## 7. LEF growth is monotone under factor maps
**Theorem M.** Let π: X → Y be a factor map of infinite minimal subshifts: continuous, onto, with π∘T_X = T_Y∘π. Then there is K ≥ 1 with `L_Y(r) ≤ L_X(Kr)` for all r. So L_Y ≼ L_X, and conjugate subshifts have ≃-equivalent LEF growth.

*Proof.*
1. *Ring map.* f ↦ f∘π is an injective unital ring homomorphism LC(Y,F_2) → LC(X,F_2), since π is onto. It is equivariant: (f∘T_Y^{-1})∘π = (f∘π)∘T_X^{-1}. So Π(Σ_j f_j u^j) = Σ_j (f_j∘π)u^j is an injective ring homomorphism R_Y → R_X. It respects u f u^{-1} = f∘T^{-1}, and it is injective coefficientwise.
2. *Group map.* Π induces an injective homomorphism GL_3(R_Y) → GL_3(R_X) with e_ij(r) ↦ e_ij(Π(r)). So it restricts to an injective homomorphism G_Y → G_X.
3. *Distortion.*
   - The generators e_ij(1) and e_ij(u^{±1}) of G_Y map to generators of G_X.
   - The generator e_ij(e_b) maps to e_ij(e_{π^{-1}[b]}). This lies in G_X and has some length K_{ij,b}, since π^{-1}[b] is clopen and G_X = EL_3(R_X).
   - Put K = max(1, max K_{ij,b}). Then |Π(g)|_X ≤ K|g|_Y, so Π maps B_Y(r) injectively into B_X(Kr).
4. *Restriction of models.* Let φ: B_X(Kr) → Q be injective with φ(gh) = φ(g)φ(h) whenever g, h, gh ∈ B_X(Kr).
   - If g, h, gh ∈ B_Y(r), then Π(g), Π(h) and Π(gh) = Π(g)Π(h) lie in B_X(Kr).
   - So φ∘Π is an injective partial homomorphism of B_Y(r).
   - Hence L_Y(r) ≤ |Q|. ∎

By Curtis–Hedlund–Lyndon, π^{-1}[b] is a union of cylinders on a window [−ρ, ρ]. So K is bounded in terms of ρ and |A| by Lemmas 1–2 of sk-lef-growth-bounds part 1. The exact value does not matter.

**Corollary M1 (lower bounds pass up to extensions).** If X factors onto a subshift Y with L_Y ≽ exp(r²), then L_X ≽ exp(r²). Examples of such Y, all unreviewed:
- Sturmian subshifts (sk-lef-growth Theorem D);
- subshifts with hypothesis (R) (part 1, Theorem R2);
- one-hole Toeplitz subshifts with bounded period ratios (part 2, Theorem T2).

**Corollary M2 (recoding).** Hypothesis (R) may be stated with a clopen set C in place of the letter a. Passing to a higher block presentation makes C a letter, and conjugacy preserves the ≃-class by Theorem M.

## 8. Thue–Morse
Let t = σ^∞(0) with σ(0) = 01 and σ(1) = 10, let X_TM be its orbit closure, and put d_n = t_n + t_{n+1} mod 2.

**Lemma TM1.** The block map y_n = 1 + x_n + x_{n+1} (mod 2) is a factor map from X_TM onto the period-doubling subshift X_PD, the orbit closure of the fixed point p of 0 ↦ 01, 1 ↦ 00.

*Proof.*
- Put q_n = 1 + t_n + t_{n+1}. From t_{2n} = t_n and t_{2n+1} = 1 + t_n:
  - q_{2n} = 1 + t_n + 1 + t_n = 0;
  - q_{2n+1} = 1 + (1 + t_n) + t_{n+1} = t_n + t_{n+1} = 1 + q_n.
- The fixed point p satisfies p_{2n} = 0 and p_{2n+1} = 1 + p_n (from 0 ↦ 01, 1 ↦ 00). By induction on n, q = p.
- The block map commutes with the shift and maps the orbit of t into the orbit of p. By continuity and compactness it maps X_TM onto the orbit closure of p. ∎

**Lemma TM2.** The period-doubling sequence is a one-hole Toeplitz sequence with p_k = 2^k, and X_PD is infinite and minimal.

*Proof.*
- p_{2n} = 0 is 2-periodic, and p_{2n+1} = 1 + p_n. By induction, p restricted to each residue class c mod 2^k with c ≠ 2^k − 1 is constant. The class 2^k − 1 carries p_{2^k n + 2^k − 1} = 1 + p_{2^{k−1}n + 2^{k−1} − 1} = … = (k mod 2) + p_n, which is not periodic because p is not periodic.
- p is not eventually periodic. Suppose p_{n+P} = p_n for all n ≥ n_0.
  - If P is even, then p_{2n+1+P} = p_{2n+1} gives p_{n+P/2} = p_n for large n, so P/2 is an eventual period. Descend until P is odd.
  - If P is odd, then for n ≥ n_0 the position 2n + P is odd and p_{2n+P} = p_{2n} = 0.
  - Writing 2n + P = 2m + 1 gives 1 + p_m = 0, so p_m = 1 for all large m.
  - That contradicts p_{2m} = 0.
- Minimality holds because σ is primitive (σ²(0) = 0100 and σ²(1) = 0101 both contain both letters). ∎

**Lemma TM3 (linear recurrence).** Every word of X_TM of length R ≥ 64n contains every word of X_TM of length n.

*Proof.* Take k with 2^{k−1} < n ≤ 2^k.
- Every factor of t of length n lies inside σ^{k+1}(ab) for some factor ab of t of length 2, because σ^{k+1}-blocks have length 2^{k+1} ≥ 2n.
- σ³(0) = 01101001 and σ³(1) = 10010110 each contain all of 00, 01, 10, 11. So σ^{k+4}(c) contains σ^{k+1}(ab) for every ab, hence every n-word, for both c.
- Any factor of length 2^{k+5} contains a full block σ^{k+4}(c).
- 2^{k+5} < 64n. ∎

**Theorem TM.** L_{X_TM} ≃ exp(r²).

*Proof.*
- *Lower bound.* Lemmas TM1–TM2, Theorem T2 of part 2 (|A| = 2, ρ = 2) and Theorem M. The letter swap conjugates X_PD with its complement, which Theorem M absorbs.
- *Upper bound.* Lemma TM3 gives R_X(n) ≤ 64n. Then sk-lef-growth Theorem A(c) gives N_X(n) ≤ 2R_X(n) ≤ 128n, so L_X(r) < 2^{9·128²(4r+1)²}. ∎

## 9. What remains
- *Covered:* every X with a factor that is Sturmian, a rotation coding with an arc letter, or a one-hole Toeplitz subshift with bounded period ratios. This includes all X with such a factor and arbitrary extra structure (entropy aside, where Theorem B already gives more).
- *Not covered:*
  - weakly mixing X, which have no eigenvalues and so none of these factors (Chacón);
  - Toeplitz subshifts with several holes per period;
  - odometer extensions that are not Toeplitz.

  Numerics for Chacón are in part 4.
