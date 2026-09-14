# sk-lef-growth-all: cheap towers beyond Sturmian (part 1: rotation factors and a general upper bound)

Lane sk-lef-growth-all, 2026-09-13. Status: written proofs, UNREVIEWED (queued with sk-referee-2).
Notation, Lemma 0 (relations transport), Lemma 1 (units are cheap), Lemma 3 (unitriangular detection), Lemma 4 (tower copy)
and Theorem C (short towers force large models) are from `research/artifacts/sk-lef-growth-bounds-2026-09-13-part{1,2}.md`.
- X ⊆ A^Z is an infinite minimal subshift, (Tx)_n = x_{n+1}, R = LC(X,F_2) ⋊ Z with u f u^{-1} = f∘T^{-1}.
- G_X = EL_3(R) with generators S = {e_ij(s) : s ∈ {1, u^{±1}, e_a}}.
- L_X(r) is Bradford's LEF growth: the least order of a finite group receiving an injective partial homomorphism of B(r).
- Theorem C: let W be nonempty clopen with W ∩ T^tW = ∅ for 0 < |t| ≤ 2m, and κ = max_{i≠j}|e_ij(e_W)|. Then
  L_X(r) ≥ 2^{d(d−1)/2} with d = 3(2m+1), for every r ≥ 20κ + 480m.

Target (O1 of sk-lef-growth): L_X ≽ exp(r²) for every X. By Theorem C it suffices to find, for all large m, a clopen W
with no returns up to 2m and κ(W) = O(m).

## 1. The letter-change trick
For a letter a and q ≥ 1 put
`W(a,q) = {x ∈ X : x_0 = a, x_q ≠ a} = [a] ∖ T^{-q}[a]`.

**Lemma 5 (cost).** |e_ij(e_{W(a,q)})| ≤ 5 + 48q for all i ≠ j.
*Proof.* e_{T^{-q}[a]} = u^{-q}e_a u^q, since u e_U u^{-1} = e_{TU}. So e_W = e_a + e_a·u^{-q}e_a u^q (char 2), and
e_ij(e_W) = e_ij(e_a)·[e_ik(e_a), e_kj(u^{-q}e_a u^q)] with k the third index. By Lemma 1 the second factor has length
≤ 2 + 2(1 + 24q). ∎

W(a,q) is cheap for every X. The question is when it has no short returns. It does when the letter a is an arc of a rotation factor.

## 2. Rotation factors
**Hypothesis (R).** There are:
- an irrational α and a continuous surjection π: X → R/Z with π(Tx) = π(x) + α;
- a letter a and a half-open arc I = [β, β') with 0 < |I| < 1 such that `π^{-1}(int I) ⊆ [a] ⊆ π^{-1}(cl I)`.

Examples:
- Sturmian subshifts (a = 1, I = [1−α, 1));
- every coding of an irrational rotation by a partition of the circle into finitely many half-open intervals, for every letter a;
- more generally, every almost automorphic subshift over an irrational rotation in which some letter is cut out by an arc.

For every rotation coding the sandwich holds because a point whose orbit avoids the partition endpoints has a unique coding,
and every point of X is a limit of such codings.

Let p_n/q_n be the convergents of α and η_n = q_nα − p_n. Best approximation (sk-lef-growth part 2 §6 step 3): for
0 < |t| < q_{n+1}, ‖tα‖ ≥ |η_n|, with equality only for t = ±q_n.

**Theorem R1 (linear-cost towers).** Assume (R). Let n be such that |η_n| < min(|I|, 1 − |I|), and put q = q_n.
Then W = W(a,q) is a nonempty clopen set with W ∩ T^tW = ∅ for 0 < |t| < q_{n+1}, and κ(W) ≤ 5 + 48q.

*Proof.* Put η = |η_n|, θ = π(x), and use qα ≡ η_n mod 1.
1. *The image is a short arc.* Suppose η_n > 0, and let x ∈ W.
   - x_0 = a gives θ ∈ cl I = [β, β'].
   - x_q ≠ a gives π(T^qx) = θ + η ∉ int I = (β, β').
   - Since |I| + η < 1, the point θ + η lies in [β + η, β' + η] without wrapping, so θ + η ≥ β'.
   - So π(W) ⊆ J = [β' − η, β'], a closed arc of length η.
   - If η_n < 0 the same argument gives π(W) ⊆ J = [β, β + η].
2. *Nonempty.* Take θ ∈ int J (η_n > 0) and x ∈ π^{-1}(θ).
   - θ ∈ int I, so x_0 = a.
   - θ + η ∈ (β', β' + η), which is disjoint from cl I because |I| + η < 1. So (T^qx)_0 ≠ a.
   - The case η_n < 0 is symmetric.
   - W is clopen, since it is a Boolean combination of cylinders.
3. *No returns.* Let x ∈ W ∩ T^tW with 0 < |t| < q_{n+1}. Then π(x) and π(T^{-t}x) = π(x) − tα both lie in J, so ‖tα‖ ≤ η.
   - By best approximation t = ±q.
   - If t = q, then T^{-q}x ∈ W gives x_0 = (T^{-q}x)_q ≠ a, contradicting x ∈ W.
   - If t = −q, then T^qx ∈ W gives (T^qx)_0 = a, contradicting x_q ≠ a.
4. *Cost.* Lemma 5. ∎

**Theorem R2 (lower bound).** Assume (R). Let n_0 be least with |η_{n_0}| < min(|I|, 1−|I|), and put m_0 = ⌈q_{n_0}/2⌉.
For every r ≥ 100 + 2400·m_0,
`L_X(r) ≥ 2^{18((r − 2500)/2400)²}`.

*Proof.*
- For m ≥ m_0 let n be largest with q_n ≤ 2m. Then n ≥ n_0, |η_n| ≤ |η_{n_0}|, and 2m < q_{n+1}.
- Theorem R1 gives W with no returns up to 2m and κ ≤ 5 + 48q_n ≤ 5 + 96m.
- Theorem C gives L_X(r) ≥ 2^{d(d−1)/2} ≥ 2^{18m²} for r ≥ 20(5+96m) + 480m = 100 + 2400m.
- Take m = ⌊(r − 100)/2400⌋ ≥ m_0. Then m ≥ (r − 2500)/2400. ∎

This recovers Theorem D of sk-lef-growth (Sturmian) with a two-letter-condition set of the same shape. Here the second
condition is the negation x_q ≠ a, which makes the argument independent of how the arc endpoints sit relative to Zα.

## 3. An upper bound from bounded special factors
Let s_X(n) = p_X(n+1) − p_X(n), and let N_X(n) be the least length of a cyclic word whose cyclic windows of length n are
exactly L_n(X) (sk-lef-growth part 1).

**Theorem U.** N_X(n) ≤ p_X(n) + (s_X(n−1) + 1)(p_X(n−1) − 1).
So if s_X ≤ S, then N_X(n) ≤ (S+2)(|A| + Sn), and by Theorem A of sk-lef-growth
`L_X(r) < 2^{9(S+2)²(|A| + S(4r+1))²}`, that is L_X ≼ exp(r²).

*Proof.* The Rauzy graph Γ_n has V = p_X(n−1) vertices and E = p_X(n) edges, and it is strongly connected by minimality.
- A strongly connected digraph has an ear decomposition: a cycle C_0 followed by E − V directed ears P_1, …, P_{E−V}, each a path whose endpoints lie in the part already built.
- Walk around C_0 from a vertex v. For i = 1, …, E−V:
  - walk inside the part already built to the tail of P_i, in ≤ V − 1 steps, since that part is strongly connected;
  - traverse P_i.
- Return to v in ≤ V − 1 steps.
- The total length is at most E + (E − V + 1)(V − 1), and every edge is traversed.
- The labels of a closed walk that covers every edge form a cyclic word whose cyclic n-windows are exactly L_n(X). ∎

**Corollary U1.** If p_X(n) = O(n), then s_X is bounded (Cassaigne's theorem on special factors of sequences with linear
complexity; RECALLED, not verified against the source here). So L_X ≼ exp(r²) for every minimal subshift of linear
complexity, including all linearly recurrent X and all codings of rotations by finitely many intervals.

For Sturmian X, s_X = 1 and Theorem U gives N_X(n) ≤ 3n + 1, against 2n + 2 in sk-lef-growth Corollary A1.

**Corollary R3.** If X satisfies (R) and s_X is bounded (for example, a coding of an irrational rotation by finitely many
intervals, given U1), then L_X ≃ exp(r²).

## 4. Where this stops
- (R) needs an irrational rotation factor together with a letter sandwiched by an arc.
  - Odometer factors: letters that factor through a clopen set of the odometer are invariant under the relevant periods, so W(a,p_k) is empty there.
  - Toeplitz points need the hole structure instead; see part 2.
- Weakly mixing X (Chacón) have no eigenvalues, so no rotation or odometer factor at all. Whether they have linear-cost towers is tested in part 2.
- Full cylinders of length ~m cost O(m²) (sk-lef-growth Lemma 2), which gives only exp(cr) for the tower method.
