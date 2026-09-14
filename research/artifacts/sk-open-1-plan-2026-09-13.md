# sk-open-1 plan: the theorem the note should end with

Lane `sk-open-1`, 2026-09-13. Lens: the single most beautiful theorem this note could end with.

## Target: normal subgroups are subsystems
Candidate theorem. Setting:
- X ⊆ A^Z is a subshift with no periodic points;
- R_X = LC(X,F_2) ⋊ Z, n ≥ 3, and G_X = EL_n(R_X);
- for a closed invariant Y ⊆ X, π_Y : G_X → EL_n(R_Y) is restriction, and E_Y is the normal closure of the e_12(e_V) with V clopen and V ∩ Y = ∅.

Statements:
- (a) SANDWICH. Every normal subgroup N satisfies E_Y ≤ N ≤ ker π_Y for exactly one closed invariant Y.
- (b) DICTIONARY (target). ker π_Y = E_Y. Then the normal subgroups of G_X are exactly the kernels ker π_Y, the quotients of G_X are exactly the groups EL_n(R_Y) of subsystems, and N ↦ Y reverses inclusion between the two lattices.
- Corollary: G_X is simple iff X is minimal. The note's Theorem becomes an iff.

## Why this one
- It turns simplicity into a dictionary between group theory and dynamics:
  - normal subgroups ↔ subsystems;
  - quotients ↔ restrictions.
- It parallels:
  - ideals ↔ open invariant sets for Steinberg algebras (Steinberg, Clark–Edie-Michell);
  - the normal-subgroup theorems for topological full groups (Bezuglyi–Medynets, Matui).
- The proof is the note's §1 run with Y in place of ∅, so the strengthening costs a few lines. The note's current proof is the case Y ∈ {∅, X}.

## Why it should be true (sketch, to be written in full)
- Ideals of R_X ↔ open invariant U. This follows from the note's e_V r e_V = e_V f_0 trick, since every point is aperiodic.
- (a) Suppose g ∈ N and π_Y(g) ≠ 1.
  - The centre of EL_n(R_Y) is trivial, because the units of LC^T(Y,F_2) are {1}. So some tower transvection h fails to commute with g modulo I.
  - Put k = [g,h]. Its corner κ is ≠ I at some point of Y. On a clopen W meeting Y where κ is constant, the note gives H_W ≤ N, so e_W ∈ I_N.
  - That contradicts W ∩ Y ≠ ∅.
- (b) The stable obstruction is ker(K_1(R,I) → K_1(R)) = K_2(R_Y)/image.
  - The algebraic Pimsner–Voiculescu / Ara–Brustenga–Cortiñas sequence gives K_2(R_Y) = 0, since K_1 = K_2 = 0 for LC(Y,F_2) (von Neumann regular, so NK-vanishing should hold).
  - At n = 3 this still needs relative injective stability. The alternative is a direct tower argument: the entries of g − I are supported on compact subsets of U.
  - THIS IS THE CRUX.

## Model tests
- Minimal X recovers the note: Y ∈ {∅, X}.
- X = Y ⊔ (an orbit of isolated points): I ≅ M_∞(F_2), the gap vanishes, and G_X/ker π_Y = G_Y.
- X = X_1 ⊔ X_2 with both minimal: G_X = G_{X_1} × G_{X_2}, with exactly 4 normal subgroups.
- A periodic orbit Y (hypothesis dropped): the quotient over F_2[t^{±1}] has congruence subgroups for every ideal. So aperiodicity is needed and the dictionary fails without it.

## Deliverables
1. Cairn:
   - an open claim `elementary-group-normal-subgroups-are-subsystem-kernels`, with Attempts;
   - an established sandwich claim with its proof route;
   - the ideal lemma;
   - the K_2 step.
2. The §6 proposal: the theorem as a final Theorem 2 or a remark, with the proof as a modification of l.154-227, targeting ≤ +8 lines.
3. A short ranking memo of ending candidates owned by other lanes, with a reader-merits recommendation:
   - universal embedding (sk-universal-embedding-a/b);
   - rigidity (sk-rigidity-*);
   - expanders (sk-expanders-limits);
   - [[T]]' ⊂ G_X (sk-subgroups);
   - the marked homeomorphism (sk-word-problem).

## Not duplicating
- sk-hypotheses-sharp shows that minimality is necessary by one example. This lane classifies ALL normal subgroups.
- sk-simplicity-short-a/b shorten the minimal case.
- sk-open-5 poses questions.
- Bounded check on main: I found no node classifying the normal subgroups of EL_n over crossed products by subsystems. The node `steinberg-algebra-simple-iff-minimal-effective` is ring level.
