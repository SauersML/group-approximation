# sk-fp-sofic-c plan (2026-09-13)

**Target.** A finitely presented infinite simple Kazhdan group that is sofic or hyperlinear. This is the root
`hyperlinear-fp-infinite-simple-kazhdan-group`, and it is Alekseev–Thom Open problem 6.1 in this form.

**Start (c).** Tracial or metric approximations that do not come from permutations of algebraic sets.

## State on main (read before planning)
- **Dead routes on the root:**
  - LEF;
  - marked limits and LEA (`fp-simple-groups-escape-soft-hyperlinear-permanence`);
  - permanence;
  - amenable orbit full groups;
  - stability.
- **Gap theorem** (sk-fp-sofic-a, `gap-sofic-approximations-are-local-embeddings`, PASS by sk-verify-3). Permutation models with
  a uniform fixed-point gap are local embeddings. Vectors, affine maps and lines over F_q are gapped.
- **Ring route, gate (c)** (`sofic-fp-simple-kazhdan-group-from-fp-simple-ring`). Rank models give only F_q-linear soficity.
- **Weak soficity** (`fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic`, unreviewed). For f.g. simple groups, weak
  soficity equals linear soficity over finite fields; the upgrade to soficity is OPEN.

## Plan
1. **Unitary gap theorem.** Let S be a finitely presented infinite simple group. Suppose a hyperlinear approximation of S
   factors as ρ_k∘φ_k: arbitrary maps φ_k into finite groups Q_k, followed by unitary representations ρ_k, and every nontrivial
   irreducible character of Q_k has |χ(q)| ≤ θχ(1) at noncentral q, for one θ < 1. Then this is impossible.
   Proof sketch:
   - Separation of one commutator bounds the trivial isotypic weight away from 1.
   - The gap then makes the relator images central.
   - That gives a homomorphism S → Q_k/Z(Q_k), which is trivial because S is infinite simple.
   - So the generators map to central elements, commutators collapse, and separation fails.
2. **Import Larsen–Shalev–Tiep** (Ann. of Math. 174 (2011)), verbatim from the source:
   |χ(g)|/χ(1) < q^{−√supp(g)/481} for finite simply connected classical groups. Noncentral g has supp(g) ≥ 1, so
   θ = 2^{−1/481} works uniformly in rank and field.
3. **Corollary.** A finitely presented infinite simple group has no hyperlinear approximation through unitary representations
   of finite simply connected classical groups. This holds with or without (T), and covers the binary Leavitt unit group,
   Caprace–Rémy lattices and any ring-route S. It rules out Weil, cuspidal and Steinberg-module models, and every permutation
   module of SL_N(F_q). So it strengthens the permutation gap theorem from vectors and lines to all actions of these groups.
4. **Gate (c).** Rank models over F_q cannot be upgraded to hyperlinear or sofic models through the representation theory of
   the finite classical groups they land in. Remaining room:
   - alternating and symmetric targets, where character ratios approach 1 at small support;
   - unbounded direct products of gapped groups;
   - unitary models that do not factor through finite groups at all.
5. **Recording.** Put the remaining room in the Attempts of the roots, queue review with sk-verify-5, and write a proposal
   (expected: no change to the note).

## Not duplicating
- sk-fp-sofic-d: group-theoretic candidates.
- sk-fp-sofic-a/b (finished): the permutation and SFT-isolation firewalls. This lane is the unitary and character-theoretic analog.
- The ex weak-sofic lanes: relator width over finite simple targets for weak soficity. That is a different metric, conjugation
  lengths rather than traces.
