---
rg: 2
id: multi-mover-collapse-criterion
kind: claim
title: The collapse criterion needs no distinguished mover
distinct_from:
  compression-torsion-collapse: That claim is the compression-form collapse (one-sided compressor, centralized witness); this is the action-form criterion over a G-set with a Kazhdan subgroup and finitely many movers, with an EXISTENTIAL conclusion over the mover set.
artifacts:
  - GroupApproximation/Sofic/AscendingHNNWreathWitness.lean
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
  - research/artifacts/multi-mover-verification-2026-08-15.md
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Sofic/BlockAmplificationRepair.lean
---

In the action-form collapse criterion (working-group Theorem 4.1: G
acting on X, a Kazhdan subgroup Gamma, basepoint x_0 with stabilizer
H, lamp generators a_x, morphisms to the matrix corona Q_d), the
single-mover hypothesis `Gamma = <H, gamma>` can be dropped: since
Gamma has (T) it is finitely generated, so Gamma = <H, gamma_1, ...,
gamma_m> with every gamma_i moving x_0 (WLOG H is the FULL stabilizer
of x_0, so generators fixing x_0 fold into H — this is the one
hypothesis to make explicit).  Normalize at k_n := max_i d_n(x_0,
gamma_i x_0); pigeonhole a subsequence where the argmax i* is
constant.  The word-length estimate delta_n(g) <= C_g k_n only ever
used "every letter's displacement is at most k_n", which the max
guarantees by definition, and the argmax mover has normalized mass
exactly 1 at the top scale, which is what the spectral-gap
contradiction consumes.  Conclusion: no injective corona representation
survives the finite mover family — existential over that family, and
sufficient for non-MF-ness whenever all these products are nontrivial.
The naive reading, "the argmax defect dies along the argmax
subsequence", is FALSE in a c_0-corona and is replaced by finite block
amplification; see the route.

Consequence (the co-Hopf reduction): a non-MF group needs only a
property (T) group that is not co-Hopfian — form the ascending HNN
G = <Gamma, t> along the proper self-embedding and take finite-order
lamps over G/Gamma.  The literal witness pair is already
kernel-checked on our side: gammaBar has (T)
(`gammaBar_hasKazhdanPropertyT`) and conjD is a proper self-embedding
(`conjD_injective`, `v1G_not_mem_range`); the skeleton with Britton
nontriviality is [[concrete-compression-source]].  Consistency: the
criterion kills finite-order lamps only, matching the kernel-checked
spectral dichotomy — [[mf-vs-tracial-radical-strict-gap]] proves the
Z-lamp wreath over the same action is MF.  The lean wreath is
finitely generated but NOT finitely presented; the finitely presented
headline still needs presentation engineering or the routing program
([[bespoke-routing-lemma]]).

Attribution.  The refinement is Francesco Fournier-Facio's: replacing the
distinguished mover by a finite mover family and normalizing by their
maximal displacement, and the consequent reduction of the construction to
a non-co-Hopfian property-(T) group.  The norm-corona implementation is
ours — his formulation passes to the argmax subsequence, which does not
vanish in a c_0-corona, and finite-family block amplification replaces
that step.  Full split in `notes/CREDIT_AND_PRIORITY_AUDIT.md`.  Verified
here independently.
Formalization surface: differs from the compression-form core only in
the estimate layer (max-displacement bookkeeping + pigeonhole), a
natural next Lean target.

## Attempts

Referee-grade verification completed 2026-08-15
(research/artifacts/multi-mover-verification-2026-08-15.md): the
argument is CORRECT as sketched.  The modification touches only the
normalization and the word-length estimate; H-letters displace exactly
zero by the wreath relation, gamma-letters displace at most the max by
definition, and the argmax mover carries normalized mass exactly one,
so both sides of the estimate survive with the same constants.

CORRECTED 2026-08-16.  The sentence previously here — "in the corona
formulation the ultrafilter performs the pigeonhole, so no subsequence
extraction is needed" — conflated the norm matrix corona
`prod M_{d_n} / sum M_{d_n}` with a norm *ultraproduct*.  In an
ultraproduct the finite pigeonhole does select a mover on a large set;
in the corona, vanishing along a subsequence is not vanishing (take
`x_n = 0` for even `n` and `1` for odd `n`), so the argmax step does not
by itself kill anything.  The repair is finite block amplification, and
it is what the route now records.  Two substantive deltas remain: H must be
the full stabilizer (generators fixing the basepoint must fold into
H), and the conclusion is existential per morphism — sufficient for
non-MF-ness since the finite blocking set is fixed in advance, but NOT
a radical-membership statement; pinning an element of Rad_MF still
requires (iii), a permuting symmetry, or the compression form.

Lean, 2026-08-16: the block repair itself is now checked, as
`Sofic/BlockAmplificationRepair.exists_stagewise_separated` and
`not_isOperatorMF_of_no_multiMarked`, the latter taking the analytic
core as its only hypothesis.  The rest of the earlier note still
stands: the kernel-checked compression-form endpoint
(`actualCoronaMFInvisible_commutator`) is universal over the whole
Kazhdan subgroup with no mover bookkeeping — a compressor buys
universality, movers buy only existence — so for our own witnesses the
finite-family corona statement is not the one being used, and a
faithful formalization of the full action form is still the rank-cocycle
analytic core held behind the `TorsionCompressionCollapse` assembly
gate, a separate project.
