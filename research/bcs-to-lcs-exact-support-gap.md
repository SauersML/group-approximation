---
rg: 2
id: bcs-to-lcs-exact-support-gap
kind: claim
title: A tracial non-RU BCS admits an LCS check distribution with exact-support mass exceeding approximate soundness
distinct_from:
  robust-locally-satisfiable-relator-code: that asks for sparse group-ball preservation with no ambient tracial witness; this target uses a tracial BCS witness to certify nontriviality of the central mark and only needs an exact-support mass gap.
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
  - docs/FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md
---

Starting from a finite BCS `B` which is tracially satisfiable but not
`R^U`-satisfiable, construct a finite **linear-system / LCS** relator menu `S`,
a distribution `mu` on `S`, a marked central involution `J`, and a tracial
unitary assignment `rho` such that, for some

```text
0 < eps < eps_plus,
delta > 0,
```

the following strict inequality holds.

Let

```text
E = {r in S : rho(r)=1 exactly},
g = mu(E).
```

Among all finite-dimensional unitary assignments with
`d_2(J,1)>=delta`, let `q` be the supremum `mu`-mass of relators whose defect
is at most `eps_plus`.  Then

```text
g > q.
```

By `exact-support-relator-sparsification`, this one inequality already
produces a finite LCS subpresentation whose solution-group mark is genuinely
nontrivial but trivial in approximate representations.  Thus **perfect
completeness of the whole LCS compiler is not required**.

## Attempts

- **Published Taller--Vidick test, unmodified.**  Their Definition 4.1 samples
  independent mask bits with `Pr[mu(phi)=1]=1-epsilon`; Lemma 4.2 shows that
  this is exactly where the honest completeness loss comes from.  If the mask
  is `+1` on every active long-code outcome of one equation, that equation is
  exact for the constructed honest strategy.  The sufficient syntactic event
  `mu identically +1` has positive but often tiny mass.  Proposition 4.1 gives
  constant finite-dimensional synchronous soundness after enough repetition.
  The unresolved numerical/structural question is whether a reweighting or
  redesign can make exact mass beat approximate satisfaction mass.
- **Perfect mask repair is not the target.**
  `docs/FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md` proves that changing only the
  mask distribution cannot make the published Fourier decoder perfectly
  complete without losing the damping needed for soundness.  That does not
  rule out the weaker strict inequality `g>q`: a positive fraction of checks
  may remain deliberately inexact in the tracial model and be discarded by
  the sparsification theorem.
- **Condition on exact-support checks.**  Let `E` be the checks exact in the
  tracial strategy and study the finite-dimensional value under the verifier
  distribution conditioned on `E`.  It is enough to prove this conditional
  value is bounded below one; the size of `E` is irrelevant after
  conditioning.  The published soundness theorem controls the unconditioned
  distribution, so a new robustness argument is required.
- **Quantum-sound gadget compiler.**  Use the 2026 weighted-polymorphism
  characterization of robust commutativity gadgets to seek a source-specific
  reduction from the known tracial/non-`R^U` BCS to LCS checks which preserves
  approximate-model soundness on the exact-support subfamily, without demanding
  a generic BCS-to-LIN homomorphism (which Paddock--Slofstra identify as the
  nonhyperlinear boundary itself).
- **Modern parallel repetition.**  The 2026 general exponential quantum
  parallel repetition theorem can make an arbitrary finite-dimensional base
  game exponentially sound under repetition.  This removes the old
  qualitative repetition uncertainty, but by itself does not compare the
  decay exponent with the growth of the honest long-code support.  The useful
  parameter is the exact-support/soundness ratio, not repeated value alone.
