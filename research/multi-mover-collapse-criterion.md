---
rg: 2
id: multi-mover-collapse-criterion
kind: claim
title: The collapse criterion needs no distinguished mover
distinct_from:
  compression-torsion-collapse: That claim is the compression-form collapse (one-sided compressor, centralized witness); this is the action-form criterion over a G-set with a Kazhdan subgroup and finitely many movers, with an EXISTENTIAL conclusion over the mover set.
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
  - research/artifacts/multi-mover-verification-2026-08-15.md
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
contradiction consumes.  Conclusion: a_{gamma_{i*} x_0} a_{x_0} dies —
existential over the finite mover set, subsequence-dependent, which
suffices for non-MF-ness whenever all these products are nontrivial.

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

Provenance: Francesco Fournier-Facio's review (email, 2026-08-15) of
the working-group criterion note; verified here independently.
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
so both sides of the estimate survive with the same constants.  In the
corona formulation the ultrafilter performs the pigeonhole (the argmax
takes finitely many values, exactly one is U-large) — no subsequence
extraction is even needed.  Two substantive deltas recorded: H must be
the full stabilizer (generators fixing the basepoint must fold into
H), and the conclusion is existential per morphism — sufficient for
non-MF-ness since the finite blocking set is fixed in advance, but NOT
a radical-membership statement; pinning an element of Rad_MF still
requires (iii), a permuting symmetry, or the compression form.  NO
Lean module written, deliberately: the kernel-checked compression-form
endpoint (`actualCoronaMFInvisible_commutator`) is universal over the
whole Kazhdan subgroup with no mover bookkeeping — a compressor buys
universality, movers buy only existence — so the finite-family corona
statement is vacuous on our side, and a faithful formalization of the
action form is the rank-cocycle analytic core held behind the
`TorsionCompressionCollapse` assembly gate, a separate project.
