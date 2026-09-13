# Idea lane nh-profile: hyperlinear profiles toward `non-hyperlinear-group`

**Date:** 2026-09-13. **Lens:** hyperlinear profile, the least dimension of a
unitary approximation with given relator defect that keeps a fixed element far
from 1. **Status:** exploration only; no node edited, nothing claimed solved.
Five approaches, one survivor (C), four killed.

## Sources checked for this lane

- Slofstra, arXiv:1806.05267, abstract: a finitely presented group with
  hyperlinear profile at least `exp(1/eps^k)` for some `0<k<1`.
- Slofstra--Vidick, arXiv:1711.10676, abstract: profiles of finitely presented
  groups control the entanglement needed to play linear-system games
  near-optimally.
- Taller--Vidick, arXiv:2507.22444, abstract: `LIN*_(1-eps,s) = RE` for every
  sufficiently small `eps>0`; "Achieving the same result with eps=0 would imply
  the existence of a non-hyperlinear group."
- Lin, arXiv:2510.07162 (extracted text, lines 915--917 and bibliography entry
  [PS25]): "It is shown in [PS25] that LinMIP*, or MIP* protocols being
  restricted to Linear Constraint System game, being computable is equivalent
  to the existence of a non-hyperlinear group." [PS25] is Paddock--Slofstra,
  arXiv:2310.07901, not opened here.
- Repo: `research/non-hyperlinear-group.md` (existence compression, JNVWY arm,
  Ideas); `research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md`
  §§2, 6, 8, 11, 12; `research/artifacts/adversarial-dimension-matched-hs-pcp-synthesis-2026-08-20.md`;
  FRONTIER entries `decidable-wp-hyperlinear-computable-microstate-modulus` [✓],
  `canonical-profile-kleene-higman` [✓], `taller-vidick-lcs-re-hardness` [✓].
- Search summaries only, not checked against source text: Becker--Lubotzky,
  "Group stability and Property (T)"; Ollivier--Wise on countable groups inside
  `Out(N)` for Kazhdan `N`; Thom's announced sofic non-residually-finite
  Kazhdan groups.

## A. Non-recursive profile growth in a uniform family

- **Idea.** Build a uniformly computable family `(G_n, w_n)` of finitely
  presented groups whose profile at `w_n` outgrows every recursive function of
  `n`, by diagonalizing over machines; then some `G_n` cannot be hyperlinear.
- **Would prove.** `non-hyperlinear-group`.
- **Kill test.** Hand argument plus repo check.
- **Result.** If every `G_n` is hyperlinear, the exact rational Cayley-unitary
  search of the HS-Dehn artifact §2(ii) halts for each `(n, eps)`, and its first
  dimension is total recursive in `n` and bounds the profile. So non-recursive
  growth is the same statement as the search failing to halt, which is
  non-hyperlinearity; the profile adds no leverage. The self-reference layer is
  already established (`canonical-profile-kleene-higman`,
  `decidable-wp-hyperlinear-computable-microstate-modulus`,
  `dimension-matched-kleene-microstate-diagonal`), and the synthesis artifact
  locates all remaining content in the constant-HS backend.
- **Verdict: killed** (restatement; duplicate of the established Kleene layer).

## B. Completeness as a supremum rather than a perfect strategy

- **Idea.** Ask for RE-hard linear-system games whose halting side has tensor
  value supremum 1 (not attained) and whose nonhalting side has value at most a
  fixed `s<1`. The commuting-operator value is attained (the commuting
  correlation set is closed), a perfect commuting-operator strategy corresponds
  to a nontrivial central phase `J` in the solution group, and HS-Dehn artifact
  §8, Proposition 8.1 turns (halting => `J != 1`) plus (nonhalting => value
  `<1`) into a non-hyperlinear solution group through the recursion theorem.
- **Would prove.** `non-hyperlinear-group`.
- **Kill test.** Literature.
- **Result.** Game values are suprema already, so this is the `eps=0` case of
  Taller--Vidick, which they state would give a non-hyperlinear group, and by
  [PS25] as quoted in Lin it is equivalent to the target. The weakening from
  attained to supremum completeness is cosmetic.
- **Verdict: killed** (restatement of the known crux).

## C. Kazhdan profile ceiling plus profile transfer

- **Idea.** Conjecture: every hyperlinear finitely generated group with property
  (T) has, at each fixed element, a hyperlinear profile bounded by a polynomial
  in `1/eps`, by some dimension-free spectral-gap compression of approximations.
  Put a group with a super-polynomial profile lower bound, such as Slofstra's
  `exp(1/eps^k)` group, inside a finitely generated Kazhdan group. Restriction
  transfers the lower bound, with constants from derivation areas of the
  subgroup's relators, so the Kazhdan overgroup would be non-hyperlinear.
- **Would prove.** A non-hyperlinear Kazhdan group.
- **Kill tests run.**
  1. Mechanism: by the Becker--Lubotzky summary, an infinite hyperlinear group
     with (T) is not HS-stable, so the ceiling cannot come from closeness to
     exact representations. It would have to compress dimension without
     rounding to an exact representation. Not a kill; the obvious mechanism is
     gone.
  2. Embedding ingredient: one search found only embeddings into `Out(N)`
     (Ollivier--Wise summary), not subgroup embeddings into Kazhdan groups.
     Unverified either way.
  3. Consistency: residually finite Kazhdan groups have bounded profile at each
     fixed element (an exact finite quotient separates it), so they don't
     refute the ceiling. The decisive test cases are hyperlinear
     non-residually-finite Kazhdan groups at a central element: Deligne-type
     central extensions, and Thom's announced examples.
- **First lemma to test.** For a non-residually-finite central extension of a
  higher-rank lattice with property (T) and central `z`, bound from above the
  least dimension of an `eps`-approximation keeping `z` far from 1, if such
  approximations exist at all. Any super-polynomial lower bound refutes the
  ceiling. A polynomial upper bound is evidence for it. Nonexistence is the
  owned `sp2g-z-full-c-star-algebra-has-llp` refutation mouth, so this lane
  would only quantify it.
- **Verdict: unclear** (survives as a testable conjecture; best survivor of the
  lane).

## D. Dimension-dependent weak stability in the centralizer-HNN theorem

- **Idea.** HS-Dehn artifact §11 proves: if `A` is flexibly HS-stable, then
  `<A, t | [t, C] = 1>` is non-hyperlinear. Replace flexible stability by a
  profile-graded weak stability, `eta(tau, d) -> 0` whenever `tau <= g(d)`, which
  quantitative (tau)-type arguments might supply for `A = SL_2(Z[1/pq])`.
- **Would prove.** `non-hyperlinear-group` through the §11 host.
- **Kill test.** Hand argument.
- **Result.** Microstates of the HNN group can be amplified, `U -> U (x) 1_k`,
  at fixed defect and fixed normalized traces, so an adversarial microstate
  sequence can always keep `tau_n >= g(d_n)`. A stability constant that degrades
  with dimension is never consumed. The only consumable variant is
  dimension-uniform stability for the `A`-parts of microstates of the HNN group,
  and §11's last paragraph already records that as equivalent to the conclusion.
- **Verdict: killed.**

## E. A self-similar profile fixed point

- **Idea.** Use a group with an amplifying endomorphism (HNN conjugation, or a
  contracting self-similar structure) that compresses any `tau`-approximation in
  dimension `d` to one in dimension `<= d/2` with defect `<= C tau`. Together
  with a subexponential profile lower bound at every scale, iteration would push
  the dimension below the lower bound.
- **Would prove.** `non-hyperlinear-group`.
- **Kill test.** Hand counting.
- **Result.** After `k = log_2 d - c` steps the dimension is about `2^c` and the
  defect is `tau d^(log_2 C)`. A lower bound `exp(tau'^(-a))` is violated only if
  `tau d^(log_2 C)` stays below a constant. For `C > 1` an adversary with
  `d >= exp(tau^(-a))` makes it blow up. Only near-isometric compression,
  `C = 1 + O(tau)`, survives, and approximate representations have no invariant
  subspaces to restrict to, so no mechanism is in sight.
- **Verdict: killed** as stated; the near-isometric variant is unclear and has no
  candidate mechanism.

## Ranking

C is the only survivor worth a deep lane, and its first lemma is a concrete
profile computation on a Deligne-type central extension. A, B, D and E are
recorded so later waves skip them.
