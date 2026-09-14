# sk-fp-sofic-d: candidate scan and affine interpolation (2026-09-13)

Lane sk-fp-sofic-d, start (d) of Q1: a finitely presented infinite simple Kazhdan group that is
sofic or hyperlinear. Unreviewed. No Cairn claim is established here: this landing adds
Attempts bullets to `km-246-lattice-is-sofic`, `hyperlinear-fp-infinite-simple-kazhdan-group`
and `hyperlinear-fp-infinite-simple-group`.

## 1. Candidate scan (bounded)

Sources: two web queries, four arXiv abstract pages, and the first three pages of one PDF.

- **López Neumann, "Finitely presented simple groups and measure equivalence", arXiv:2101.09071v2.**
  Read from the PDF, pages 1–2.
  - Abstract: "We exhibit explicit infinite families of finitely presented, Kazhdan, simple groups
    that are pairwise not measure equivalent. These groups are lattices acting on products of
    buildings."
  - Introduction: "Infinite finitely presented simple groups are rare in geometric group theory.
    To this date, few examples are known: Burger-Mozes groups acting on products of trees [BM00],
    non-affine irreducible Kac-Moody lattices over a finite field acting on twin buildings [CR06]
    and variants of Thompson groups [Rö99]."
  - Theorem 1.1: "There are infinitely many measure equivalence classes containing finitely
    presented, Kazhdan, simple groups. These groups are Kac-Moody lattices over finite fields with
    well-chosen non-affine Weyl groups."
  - Mechanism, p. 1–2: for every n there is such a lattice Λ_n with β^{d(n)}(Λ_n) > 0 and
    β^k(Λ_n) = 0 for k > d(n), where d(n) → ∞.
  - Verdict: no new family. For the measure-equivalence route of `km-246-lattice-is-sofic`, a
    donor lattice in Păunescu's class must be Kazhdan (Furman: (T) is an ME invariant) and must
    have the same ℓ²-Betti profile up to proportionality (Gaboriau).
- **Amir–Lazarovich, "Simple Lattices in Products of Davis Complexes", arXiv:2605.09493.** Abstract
  through the fetch tool: "lattices in products of trees and two-dimensional Davis complexes of the
  right-angled Coxeter group whose defining graph is an odd graph".
  - Davis complexes of right-angled Coxeter groups, and their products with trees, are
    finite-dimensional CAT(0) cube complexes. So these simple uniform lattices have the Haagerup
    property (Niblo–Reeves, 1997), and an infinite Haagerup group is not Kazhdan.
  - They act properly and cocompactly on a contractible complex, so they are finitely presented.
  - Verdict: candidates for the version of Q1 without (T), `hyperlinear-fp-infinite-simple-group`,
    with no recorded approximation status.
- **Chatterji–Kassabov, arXiv:2601.22907.** Abstract: "We construct a finitely presented group
  with property (T) which can not act on on reasonable spaces. Such group is constructed using an
  generalization of Hall embedding theorem, where property (T) is added at the expense of
  weakening the simplicity requirement." Verdict: not simple, so not a candidate.
- **Fournier-Facio, arXiv:2512.09180.** Abstract: "finitely presented, Frobenius stable, have
  property (T), but are very far from having property (T₂)". Verdict: nothing about simplicity or
  soficity; not a candidate.

So the recorded fp infinite simple Kazhdan candidates stay as they were:
- the Caprace–Rémy lattices, with the explicit (2,4,6) instance (`km-246-lattice-is-sofic`);
- the Titz Mite–Witzel kernels (`titz-witzel-soficity-is-one-finite-csp`);
- the binary Leavitt unit group, which is nonsofic, with hyperlinearity open.

## 2. Affine interpolation is dead

**Setting.** Take the (2,4,6) Levi triangle recorded in `km-246-lattice-is-sofic`:
- vertex groups L_12 = T.(SL_2(q)×SL_2(q)), L_13 = T.Sp_4(q), L_23 = T.G_2(q), with q ≥ 4;
- edge groups L_1, L_2, L_3, each of the form T.SL_2(q);
- face group T.

Λ_q is the colimit. By `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, a model
that does not collapse has exact vertex actions that are free off Fix_n, with the edge actions
agreeing off o(d_n) points.

**Idea tested.**
- The affine types (2,4,4) and (2,3,6) have exact finite developments: congruence quotients of
  Sp_4(F_q[t,t^(-1)]) and G_2(F_q[t,t^(-1)]).
- (2,4,6) differs from each in one vertex group.
- Glue the (12,13)-part of a (2,4,4)-development to the (12,23)-part of a (2,3,6)-development along
  a common free L_12-action, and hope the two L_3-actions almost agree.

**Proposition (firewall).** Let σ_n be a model of the (2,4,6) triangle as above, and let c > 0.
Suppose that on a σ_n(L_12 ∪ L_13)-invariant set Y_n with |Y_n| ≥ c d_n, the action of L_2 *_T L_3
(restricted from L_12 and L_13) factors through a finite group H with no quotient containing
G_2(q). Then |Y_n \ Fix_n| = o(d_n).

**Proof.**
1. Every relator of H, as a word in L_2 ∪ L_3, holds exactly on Y_n. Every relator of L_23 holds off
   o(d_n) points, because the L_23-charts are exact and their L_2-, L_3-restrictions agree with the
   given actions off o(d_n) points.
2. Let Q be the pushout of H ← L_2 *_T L_3 → T.G_2(q).
   - Q is a quotient of T.G_2(q). The derived subgroup G_2(q) is simple for q ≥ 3, so either the
     kernel meets G_2(q) trivially or it contains G_2(q).
   - In the first case Q contains a copy of G_2(q), and Q is also a quotient of H, which no quotient
     of H can be.
   - So Q is a quotient of the abelian group T.G_2(q)/G_2(q), and every element of the perfect group
     SL_2(q) ≤ L_2 is trivial in Q.
3. Since Q = (L_2 *_T L_3)/⟨⟨rel(H) ∪ rel(L_23)⟩⟩ and L_2, L_3 are finite, each x ∈ SL_2(q) is a
   product of boundedly many conjugates of these relators. The bound depends only on q.
4. So σ_n(x) fixes all but o(d_n) points of Y_n. On Y_n \ Fix_n the L_12-charts are free off o(d_n)
   points, so |Y_n \ Fix_n| = o(d_n). □

**Instance.** In the glued model the (12,13)-part comes from an exact (2,4,4)-development. There
L_2 and L_3 generate exact T'.Sp_4(q)-charts on every point, so Y_n = [d_n] and H = T'.Sp_4(q).
Since |G_2(q)| = q^6(q^6−1)(q^2−1) > |Sp_4(q)|, no quotient of H contains G_2(q). So the glued model
collapses.

**Caveat.** Identifying the (2,4,4) vertex groups with the (2,4,6) ones needs the torus actions on
the root groups to match. The generalized Cartan matrices differ, so the identification may fail
before the argument starts. The proposition does not need it: it only assumes exact actions of the
(2,4,6) groups L_12 and L_13 whose L_2 *_T L_3 action factors through such an H on a positive
proportion of points.

**What remains, as a necessary shape.** A sofic model's (12,13)-part (a virtually free group
action) must carry approximate G_2(q)-relations in L_2 ∪ L_3 on almost every point, and exact
Sp_4(q)- and SL_2(q)²-charts. No exact development of another rank-3 triangle with these two vertex
groups supplies that. This is the recorded one-stable-letter form, seen from the affine side.

## 3. Verdict for the note

No change. The note's sentence "We do not know whether some finitely presented infinite simple
Kazhdan group is sofic" stays accurate, and nothing here enters the manuscript.

## 4. Sharpest next targets (none needs a lane family)

- A model of the virtually free group L_12 *_{L_1} L_13 in which L_2 ∪ L_3 satisfies the
  G_2(q)-relations off o(d_n) points without collapsing. That is the gate itself, for
  q = 4: SL_2(4)², Sp_4(4), G_2(4).
- For the measure-equivalence route: a Kazhdan group in Păunescu's class with the (2,4,6)
  ℓ²-Betti profile, or a proof that no Kazhdan group in that class has high-degree ℓ²-Betti
  numbers.
