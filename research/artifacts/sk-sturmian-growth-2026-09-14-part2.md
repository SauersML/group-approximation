# sk-sturmian-growth part 2: a K-theoretic obstruction to uniform level models, and where remainder linking dies (2026-09-14)

Lane sk-sturmian-growth. Plan: `research/artifacts/sk-sturmian-growth-plan-2026-09-14.md`. Status: established routine lemmas and recorded attempts; no new theorem about Sturmian growth.

## 1. Uniform level models force a divisible unit in K^0
The Sauer–Schesler engine for [[T]]′ (sk-cornulier-q7, and Theorem Q′ in the plan) needs a **uniform level model** at every good scale:
- a clopen V;
- a finite level set Y with |Y| = N;
- local-pseudogroup maps φ_y: V → X with X = ⊔_{y∈Y} φ_y(V).

Then level permutations L_π(φ_y(v)) = φ_{πy}(v) lie in [[T]]. The dyadic case uses N = 8·2^n and φ_y = T^{β(y)}.

**Lemma K.** If (X,T) is a minimal Cantor system with such a model, then [1_X] = N·[1_V] in K^0(X,T) = C(X,Z)/{f − f∘T}.
- *Proof.* φ_y(V) and V are equivalent under the local pseudogroup of T, so 1_{φ_y(V)} − 1_V is a coboundary, and [1_{φ_y(V)}] = [1_V]. Summing over y gives [1_X] = N[1_V]. ∎
- Equivalently, μ(V) = 1/N for every invariant probability μ.

**Corollary K1.** A Sturmian subshift X_α (α irrational) admits no uniform level model with N ≥ 2, even with piecewise (non-uniform) level maps.
- K^0(X_α,T) ≅ Z + αZ ⊂ R, ordered by R, with unit 1.
  - This is the standard computation for Sturmian systems: the dimension group of the rotation coding. It is recalled, not re-read at source.
- 1/N ∈ Z + αZ forces N = 1.
- More simply: X_α is uniquely ergodic, and the measures of clopen sets lie in (Z + αZ) ∩ [0,1], which contains no 1/N for N ≥ 2.

**Consequence for the method.**
- The dyadic engine needs 2^m | [1_X] in K^0 at infinitely many scales.
- For Sturmian subshifts, and for every minimal subshift whose unit class has no 2-divisibility, every level model leaves a **remainder** of positive measure outside the uniform part.
- So remainders are unavoidable, and any proof for them must handle levels with non-uniform bases.

This sharpens the plan's Lemma O (no constant towers): even orbit-rearranged level structures are excluded.

## 2. R2 dies at counting when remainders are linked by a bounded generator
**Attempt.** Rauzy towers at scale n have heights q_n, q_{n−1} over W = A ⊔ B.
- Put the dyadic block D ⊆ {0,…,q_{n−1}−1} (common levels) with |D| = 8·2^k ≤ q_{n−1}, and run types 1–4 inside W × D.
- To reach the remaining common levels, add one uniform level permutation c acting transitively on L_common, e.g. a long cycle.
- Generation would follow: Alt(D) plus a transitive c on L_common gives a primitive group containing a 3-cycle, hence Alt(L_common) (Jordan).

**Where it dies.** The counting of part 2 §6 needs the conjugates of the linking generators by short words to commute.
- The conjugates c^g (g a Grigorchuk word) all move the remainder levels, so their supports overlap.
- Already ⟨c, t⟩ with t a transposition has exponential ball growth up to radius comparable to q_{n−1}: the transpositions c^k t c^{−k} are distinct for |k| < q_{n−1}/2, and products of them along words of length ℓ give about 2^{ℓ/2} distinct permutations.
- So γ^{T_n}(ℓ) ≥ 2^{cℓ} for ℓ up to about q_{n−1}, and no small-ball bound survives.
- The dyadic case avoids this only because D is all of Y (no remainder).

**What a proof for Sturmian subshifts would need** (sharpest target):
- a bounded-size family of level permutations acting on the Rauzy level sets (all levels of both towers);
- with intermediate growth estimates for its truncations (analogue of SS1–SS2), separation of two base points (SS3) and connectivity (SS4);
- with the tower heights q_n, q_{n−1} in place of 2^n.

The Grigorchuk group's level-n Schreier graphs are paths of length 2^n. A group of intermediate growth whose finite actions realize paths of lengths q_n, compatibly with the Rauzy concatenation A_{n+1} = A_n^{a_{n+1}}B_n, is what is missing. I did not find one; this is a bounded check from memory, not a literature search.

## 3. Status of the question for Sturmian subshifts
Open. The obstruction of §1 shows the known engine cannot apply directly, and §2 records the first natural repair and why it fails. A uniform-growth proof (plan R3) is not attempted.
