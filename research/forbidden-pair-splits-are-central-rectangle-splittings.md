---
rg: 2
id: forbidden-pair-splits-are-central-rectangle-splittings
kind: claim
title: On a perfect trace the forbidden-pair commutation split is orthogonality of central supports in the pair algebra, so it equals the rectangle splitting and every constraint-variable gap source passes it
distinct_from:
  hidden-labels-import-cross-context-commutation: that derives the forbidden-pair split from a coset refinement of the context game; this shows that on perfect traces the split is equivalent to orthogonal central supports and to the two-question rectangle splitting, and that a gap source whose every perfect trace passes it exists.
  coset-refinement-forces-rectangular-central-splitting: that derives (RCS) from a coset refinement of the synchronous game itself; this proves that the three-context split forced by refinements of the one-hot/NAND context game is already equivalent to (RCS), and gives the word criterion.
  oracularizable-tracial-nonru-game-exists: that supplies an incidence-oracularizable gap game for the long-code route; this uses the elementary constraint-variable presentation only to show that the forbidden-pair split is not an obstruction.
---

**ESTABLISHED** by `forbidden-pair-splits-are-central-rectangle-splittings-proof`.
Not reviewed by an ex-verify lane.

**Setting.**
- `G` is a finite synchronous game with questions `Q` and answer sets `A_q`.
- A *forbidden pair* is `(a,a')` for `q != q'` with `V(q,q';a,a') = 0` or
  `V(q',q;a',a) = 0`, as in MSSV, arXiv:2505.05253, Definition 2.7.
- `tau` is a *perfect trace*: a faithful normal trace on a von Neumann
  algebra `M` with PVMs `P_q` such that `P_q^a P_(q')^(a') = 0` on forbidden
  pairs.
- `N = N_(qq') = W*(P_q, P_(q'))`.  For a projection `e in N`, `C(e)` is its
  central support in `N`.

**Theorem.**  For a forbidden pair `(a,a')` of `(q,q')` the following are
equivalent.

- **(FS)** There is a projection `m in M` commuting with `P_q` and `P_(q')`
  such that, for all answers `b` of `q'` and `b'` of `q`,
  `[P_q^a, P_(q')^b] m = 0` and `[P_(q')^(a'), P_q^(b')] (1 - m) = 0`.
  This is the split of Corollary 2 of
  `hidden-labels-import-cross-context-commutation`.
- **(CS)** `C(P_q^a) C(P_(q')^(a')) = 0`.
- **(W)** `P_(q')^(a') x P_q^a = 0` for every `x in N`.  Equivalently this holds
  for every alternating word `x = P_q^(c_1) P_(q')^(d_1) ... P_(q')^(d_k)`.

Moreover, (CS) holds for every forbidden pair of `(q,q')` iff `N_(qq')`
satisfies (RCS) of `coset-refinement-forces-rectangular-central-splitting`.

**Corollaries.**
1. **No new firewall on one-hot/NAND presentations.**  A perfect trace passes
   every forbidden-pair split iff it satisfies (RCS) on every question pair
   of `G`.  So on these presentations the three-context theorem forces
   nothing beyond the two-question one.
2. **Commuting pairs pass.**  If `P_q` and `P_(q')` commute whenever `(q,q')`
   carries a forbidden pair, then `C(e) = e` in the abelian `N`, and (CS) is
   perfection.  Every split holds, with `m = 1 - P_q^a`.
   - Lin's *oracularizable* strategies (arXiv:2510.07162v1, Definition 3.15:
     commutation whenever `mu(x,y) > 0`) pass, provided `V = 1` off
     `supp mu`.  That convention changes no game value, and MSSV's
     Theorem 3.1 needs it, since its game graph joins `V = 0` pairs whatever
     `mu` is.
3. **A gap source on which every perfect trace passes.**  Let `B` be a
   Boolean constraint system.
   - **Its constraint-variable game `G_cv(B)`.**  Questions are the contexts
     `c`, with answers `Allowed_c`, and the variables `v`, with answers
     `Z_2`.  The forbidden pairs are `(a,b)` on `(c,v)` with `v in c` and
     `a_v != b`.
   - **Properties.**  In every perfect trace, `P_v` is a function of `P_c`,
     so every pair algebra that carries a forbidden pair is abelian.  Also
     `A(G_cv(B)) ≅ A(B)`.
   - **The gap source.**  Take `B = B_I` of
     `perfect-qc-separation-yields-finite-bcs-with-no-matrix-model` (PQB4).
     Then `G_cv(B_I)` has a perfect trace and no perfect `R^U` model, and
     every perfect trace of it passes every forbidden-pair split and every
     (RCS) condition.
4. **Consequence for the torsor route.**
   - The forbidden-pair split does not close the torsor route for Boolean
     sources.
   - What remains is to lift a trace to a coset refinement.
   - In the constraint-variable presentation, every edge `(c,v)` shares one
     variable.  So `exact-label-coset-refinements-are-affine` confines
     label-exact refinements to affine allowed sets.  A gap beyond the goal
     needs *hidden labels* on the variable questions: blocks of the refined
     `p_v` finer than the two fibres of `x_v`.

**Status of Lin's sources (read at source, arXiv:2510.07162v1).**
- **Compression steps.**  The completeness clauses of Theorem 6.5 and of the
  answer-reduction and parallel-repetition steps preserve "a perfect
  oracularizable strategy ... in model t".
- **The no case.**  Theorem 6.15, in the paragraph after it, states the no
  case only as `omega^co(G) = 1` and `omega^*(G) <= 1/2`.  Since `C_qc` is
  closed, this gives a perfect commuting strategy, but the text does not say
  that the strategy is oracularizable.
- **So for Lin's original games.**  Corollary 2 applies only where an
  oracularizable perfect strategy is known.  Corollary 3 settles the question
  for a gap source with the same algebra.

**Model tests.**
- **A classical solution passes.**  `N = C`.
- **A factor model fails.**  Take the `M_3` model of
  `coset-refinement-forces-rectangular-central-splitting`, with forbidden
  pair `(1,1)`.  `N = M_3`, so both central supports are `1` and (CS) fails.
  Hence (FS) fails too, as Corollary 2 of the hidden-labels node says.
- **A noncommuting pair passes.**
  - Take answers `{1,2,3}` on both questions and `N = M_2 ⊕ C`.
  - On `M_2`: `P_q = (e_11, e_22, 0)` and
    `P_(q') = (f, 1 - f, 0)`, with `f` the projection onto `(e_1+e_2)/sqrt2`.
  - On `C`: both questions answer `3`.
  - Forbidden pairs: `(1,3), (2,3), (3,1), (3,2)`.
  - Every product over a forbidden pair is `0`, and
    `C(P_q^1) = 1 ⊕ 0`, `C(P_(q')^3) = 0 ⊕ 1`.  So (CS) holds while `N` is
    noncommutative.
