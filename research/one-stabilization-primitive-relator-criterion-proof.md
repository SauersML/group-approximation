---
rg: 2
id: one-stabilization-primitive-relator-criterion-proof
kind: route
title: Proof of the primitive-relator criterion for one-stabilization AC-triviality
target: one-stabilization-ac-trivial-from-primitive-relator
requires:
  - z-presentations-with-a-trivializing-relator-are-ac-equivalent
---

Notation as in the target. F = F(a, b, c). "AC-trivial" means reachable from
⟨a, b, c | a, b, c⟩ by (AC1)–(AC3) in rank 3. AC-equivalence is symmetric, since each
move has an inverse composite.

**Composite moves.** Conjugating r_i by an arbitrary word u is a composite of (AC3),
applied letter by letter. So r_i ↦ r_i · u r_j^{±1} u^{−1} is a composite: conjugate r_j
by u, invert it if needed, apply (AC1), then conjugate r_j back by u^{−1}. Every
elementary Nielsen move on a triple is a composite:
- r_i ↦ r_i r_j^{±1} is (AC1), with (AC2) twice for the inverse;
- r_i ↦ r_j^{±1} r_i is r_j^{±1}(r_i r_j^{±1})r_j^{∓1}, i.e. (AC1) followed by
  conjugation;
- r_i ↦ r_i^{−1} is (AC2);
- a transposition (p, q) ↦ (q, p) is (p, q) → (pq, q) → (pq, q^{−1}) → (pq, q^{−1}pq)
  → (pq, p) [conjugate the second entry by q] → (pq, p^{−1}) → (pqp^{−1}, p^{−1})
  → (q, p^{−1}) [conjugate the first entry by p^{−1}] → (q, p).

**Step 0 (property T).** For a Z-pair r = (r_1, r_2), say T(r) holds if
⟨F | r_1, r_2, w⟩ is AC-trivial for some w with ⟨F | r_1, r_2, w⟩ = 1. By
`z-presentations-with-a-trivializing-relator-are-ac-equivalent` (n = 3, applied to the
Z-presentation ⟨F | r_1, r_2⟩), all trivializing w give one AC class. So T(r) holds iff
⟨F | r_1, r_2, w⟩ is AC-trivial for **every** trivializing w.

**Step 1 (start).** ⟨F | s_1, s_2⟩ = S * ⟨c⟩ ≅ Z, and w = c trivializes. So S⁺ is
AC-trivial iff T(s_1, s_2).

**Step 2 (P1 preserves T).** A move (P1) does not change the normal closure
N = ⟨⟨r_1, r_2⟩⟩, so the image is again a Z-pair and every trivializing w stays
trivializing. For such w, the same move applied to the first two relators of
⟨F | r_1, r_2, w⟩ is an AC move. So T(r) ⇔ T(r′).

**Step 3 (P2 preserves T).**
- (i) *Automorphisms map AC paths to AC paths.* Let α ∈ Aut(F) and let Q ↦ Q′ be an AC
  move on triples. Then α(Q) ↦ α(Q′) is a composite of AC moves: products and inverses
  map to products and inverses, and conjugation by a letter g maps to conjugation by
  the word α(g).
- (ii) *Bases are AC-trivial.* If (u_1, u_2, u_3) is a basis of F, Nielsen's theorem
  gives a sequence of elementary Nielsen moves carrying it to (a, b, c). Each such move
  is a composite of AC moves, as shown above.
- (iii) *Conclusion.* If Q is AC-trivial, then α(Q) is AC-equivalent to
  α(⟨a, b, c⟩) = ⟨α(a), α(b), α(c)⟩, which is AC-trivial by (ii).

Now let r be a Z-pair and w trivializing for r. Then α(r) is a Z-pair, because α
induces ⟨F | r⟩ ≅ ⟨F | α(r)⟩, and α(w) trivializes α(r). By (iii), T(r) implies
T(α(r)). Applying the same to α^{−1} gives the converse.

**Step 4 (endpoint).** Suppose r = (r_1, r_2) is a Z-pair with r_1 primitive; the case
of r_2 is symmetric.
- (i) *Normalize r_1.* Pick α ∈ Aut(F) with α(r_1) = a. By Step 3, T(r) ⇔ T(a, t) with
  t = α(r_2).
- (ii) *Delete a from t.* Write t = t_0 a^{e_1} t_1 ⋯ a^{e_k} t_k with t_i ∈ F(b, c). Put
  t′ = t_0 t_1 ⋯ t_k. Then t^{−1} t′ is a product of conjugates of a^{±1}. Multiplying
  the second relator on the right by these conjugates, one at a time, is a sequence of
  (P1)-composites, as in the composite-move paragraph. So T(a, t) ⇔ T(a, t′).
- (iii) *t′ is primitive in F(b, c).* ⟨b, c | t′⟩ ≅ ⟨F | a, t′⟩ ≅ Z. Let
  π: F(b, c) → Z be a surjection with kernel ⟨⟨t′⟩⟩. Then π(b), π(c) are coprime.
  - Some M ∈ GL_2(Z) carries (π(b), π(c)) to (0, 1).
  - The map Aut(F_2) → GL_2(Z) is surjective, so there is γ ∈ Aut(F(b, c)) with
    π∘γ(b) = 0 and π∘γ(c) = 1.
  - Hence ⟨⟨γ^{−1}(t′)⟩⟩ = ker(π∘γ) = ⟨⟨b⟩⟩.
  - By Magnus' theorem, if two elements of a free group have the same normal closure,
    each is conjugate to the other or its inverse (Lyndon–Schupp, Combinatorial Group
    Theory, Prop. II.5.8). So γ^{−1}(t′) = g b^{ε} g^{−1}, and t′ = γ(g) γ(b)^{ε} γ(g)^{−1}.
- (iv) *Choose w.* Extend γ to F by a ↦ a and take w = γ(c). Then
  ⟨F | a, t′, γ(c)⟩ is AC-equivalent to ⟨F | a, γ(b), γ(c)⟩: conjugate the second
  relator by γ(g)^{−1} and apply (AC2) if ε = −1. This is a basis, hence AC-trivial by
  Step 3(ii). In particular w trivializes, so T(a, t′) holds.

**Assembly.** Moves (P1) and (P2) carry (s_1, s_2) to r, and T is invariant under both
moves (Steps 2 and 3). T(r) holds by Step 4. Hence T(s_1, s_2) holds, and S⁺ is
AC-trivial by Step 1. ∎

**Step 5 (projection).** Let r = (r_1, r_2) be a Z-pair and let E be its 2 × 3 matrix of
exponent sums. For a letter g, let m_g be the 2 × 2 minor of E that omits the column of g.
- (i) *When g trivializes.* ⟨F | r⟩ ≅ Z is abelian, so it equals its abelianization
  Z³/L, where L is the row lattice of E. A linear form Z³ → Z with kernel L is
  ±(m_a, −m_b, m_c), so g maps to ±m_g. Hence w = g trivializes r iff m_g = ±1.
- (ii) *Delete g.* Suppose m_g = ±1 and let P: F → F(h, k) kill g, where h, k are the
  other two letters. Deleting every g^{±1} from r_1 and r_2 multiplies each of them by
  conjugates of g^{±1}. As in Step 4(ii), ⟨F | r_1, r_2, g⟩ is AC-equivalent to
  ⟨F | P(r_1), P(r_2), g⟩. This is the one-stabilization P(r)⁺ of the rank-2 balanced
  presentation P(r) = ⟨h, k | P(r_1), P(r_2)⟩, which presents ⟨F | r, g⟩ = 1.
- (iii) *Conclusion.* By Step 0, T(r) ⇔ P(r)⁺ is AC-trivial. With Steps 1–3: if moves
  (P1), (P2) carry (s_1, s_2) to r, then S⁺ is AC-trivial iff P(r)⁺ is AC-trivial.
- (iv) *Rank-2 moves.* AC moves on P(r) are AC moves on P(r)⁺. An automorphism of F(h, k)
  extends to F by fixing g, and it preserves AC-triviality of triples by Step 3(iii).
  So the AC class of P(r)⁺ depends only on the class of P(r) under rank-2 AC moves and
  Aut(F(h, k)).

**Remark (calibration).**
- The search goal can never be reached from the pair (a², b³) of the non-trivial
  group S = Z/2 * Z/3. Moves (P1), (P2) preserve the isomorphism type of ⟨F | r_1, r_2⟩.
  A primitive entry would, after Step 4(i)–(ii), make that group the 2-generator
  one-relator group ⟨b, c | t′⟩. But ⟨a, b, c | a², b³⟩ = Z/2 * Z/3 * Z has rank 3 by
  Grushko, so it is not 2-generated. The script finds no goal for (a², b³) at caps 9, 11
  and 13, as it must.
- AK(2) = ⟨a, b | a²b^{−3}, abab^{−1}a^{−1}b^{−1}⟩ reaches the goal in two AC products,
  which matches its known AC-triviality.
