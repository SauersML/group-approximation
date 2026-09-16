---
rg: 2
id: bk-type-i-stably-finite-algebras-are-qd
kind: claim
title: Every separable stably finite type I C*-algebra is quasidiagonal
distinct_from:
  stw99-problem-vii-blackadar-kirchberg: that is the full nuclear stably finite question; this is its type I case, which it implies because type I algebras are nuclear, and which is equivalent to the K_0-embedding property for quasidiagonal type I algebras.
  bk-t1-primitive-spectrum-case: that is the T_1 spectrum case, whose difficulty is the simple case; this is the type I case, where simple subquotients are elementary and the difficulty is entirely the gluing of CCR subquotients along singular boundary maps.
  bk-radical-projection-quotients-are-toeplitz-infinite: that describes the Toeplitz-like shape a type I counterexample would have; this is the positive question itself, reduced to a K-theoretic embedding property.
  bk-primitive-quotients-qd-or-traceless-force-qd: that is the fibrewise sufficient condition; this is the type I question, which the fibrewise condition does not reach, as the Toeplitz pair algebra shows.
  bk-projection-generated-ideals-with-uct-quotients-force-qd: that settles type I algebras with finitely many ideals, where all boundary maps vanish; this is the general type I case with nonzero singular boundaries.
artifacts:
  - research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md
---

**OPEN.**  Let `E` be a separable, stably finite type I (postliminal)
C\*-algebra.  Then `E` is quasidiagonal.

This is the type I case of STW Problem VII.  Literature status, as of
2026-09-16: no proof was found.  Brown--Dadarlat (arXiv:math/0008182), Brown's
survey (arXiv:math/0008181) and the known-case list in Moutzouris
(arXiv:2112.03224v3) do not mention type I algebras.  Spielberg's 1988 paper on
AF embeddings of extensions was not reachable, so partial prior results there
are possible.  By Theorem A of the artifact it is
*equivalent* to `type-i-qd-algebras-have-k0-embedding-property`, i.e. to (b)
below.  Via Brown--Dadarlat Theorem 4.12 it is also equivalent to the
K_0-Hahn--Banach property for separable QD type I algebras.

- (b) Every separable quasidiagonal type I algebra has the K_0-embedding
  property.
- (c) For `A` separable, QD and type I, an extension
  `0 → K⊗A → E → ⊕_N C(T) → 0` is QD iff it is stably finite.
- (e) For `A` separable, QD and type I, every `x ∈ K_0(A)` with
  `Zx ∩ K_0^+(A) = {0}` is killed by some embedding of `A` into a QD algebra.

Known cases (artifact §4, Corollary B):

- all successive boundary maps `K_1(I_{α+1}/I_α) → K_0(I_α)` along a
  composition series with CCR subquotients vanish, with no finiteness
  hypothesis; for example, finitely many ideals;
- every ideal `I_α` of the series has the K_0-embedding property, for example
  stably commutative, AF, or locally in Moutzouris' class `Y`;
- CCR algebras, including `T_1` spectrum (`separable-ccr-algebras-are-quasidiagonal`).

## Attempts

- **Reduction to the embedding property (done).**  Route
  `bk-type-i-case-via-k0-embedding`: transfinite induction up a composition
  series.
  - At a successor step the quotient is CCR, hence QD, nuclear and UCT, and the
    ideal inherits stable finiteness.
  - Spielberg makes the boundary singular.
  - Brown--Dadarlat Proposition 4.6 glues.
  - The converse is route `type-i-k0-embedding-from-type-i-case`.
- **Top-down induction fails.**  Quotients of stably finite type I algebras need
  not be stably finite: `T'/(0 ⊕ K)` is the Toeplitz algebra
  (`toeplitz-pair-algebra-is-qd-with-non-qd-irreps`).
- **Fibrewise sufficient conditions are not necessary.**  The quasidiagonal
  type I algebra `T'` has no separating family of irreducible representations
  with QD images.  Its primitive quotients `T` are traced and not QD, so the
  hypothesis of `bk-primitive-quotients-qd-or-traceless-force-qd` fails for
  `T'`.  A fibrewise hypothesis of this kind therefore fails for some QD, hence
  stably finite, type I algebras, and cannot by itself establish this claim.
- **Direct killing of singular classes (partial).**  Artifact §6.2, Lemma 4,
  sketched.  In a CCR algebra, a class whose rank function on the spectrum
  changes sign, or vanishes on a dense set, is killed by direct sums of
  compressions of irreducible representations.
  - This dies for one-signed rank functions with non-dense zero set.  An
    example is `(β, 1)` in `C(S²) ⊕ C`, which needs fuzzy-sphere
    almost-representations.
  - It also dies at Toeplitz points, where compressions are not almost
    multiplicative (§6.3).
- **Permanence under extensions (circular).**  Deducing (b) from its CCR case
  needs the K_0-embedding property to pass to extensions, which is the gluing
  problem again (§6.3 (γ)).
