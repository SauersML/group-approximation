---
rg: 2
id: fpbs-relative-cycle-block-localization
kind: claim
title: Near-optimal source graphings admit weighted boundary localization of their relative cycle surplus
distinct_from:
  fpbs-bernoulli-cycle-tail-compactness: that controls the entire cycle dimension of Bernoulli minimizers and implies cost--Betti equality; this controls only the relative projection across a specified factor
  fpbs-correlated-reuse-flags-removable: that asks for vanishing conditional traffic defect; this asks for an explicit block-boundary estimate on relative cycle operators and uses a different connected rounding construction
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

**OPEN.** For every free p.m.p. factor pi:Y->X of an infinite finitely
generated group, find finite-label generating source graphings Phi_n
with c(Phi_n)->C(Y). Let H_n be their conditional-support base graphings,
K_n their relative cycle operators, and d_n a degree bound for H_n.
Find measurable partitions E_n into H_n-connected blocks of size at
most M_n such that, writing P_out,n for the crossing-edge projection,

    (1+2 d_n M_n^2) Tr(P_out,n K_n) -> 0.

## Attempts

`fpbs-sparse-base-connected-cycle-rounding` now gives an alternative
connected surgery when the relative certificate is supported on a
sufficiently sparse base region with a fixed finite label set, for an
exact group and Bernoulli base. It uses a base-measurable separator from
Fraczyk plus Lovasz, and pays actual cut rank rather than M^2 times
boundary trace. The required sparse support does not follow from this
node's premise or from rarity of source reuse flags. It is not a proof
of this universal localization assertion.

Impose a common finite-block forest at the cost infimum. Section 5 of
the artifact justifies this without a finite normal subgroup, but
proves that a potential cost gap scales as D=q D_A under contraction.
It supplies neither this weighted boundary estimate nor the required
finite-label presentations.

Use determinantal rounding of K_n. This can disconnect even for a
finite extension with a source treeing. The replacement in Section 6
does preserve connectivity, but only yields a small error when the
displayed localization estimate holds. Merely taking larger blocks or
showing their weighted boundary tends to zero omits the factor M_n^2.

No universal construction establishing this premise is known here.
For the fixed source treeing on F_r x C_M in Section 2, Section 6
proves Tr(P_out K)>=(r-1)/4 for every finite-block partition: every
edge lies on a square and horizontal tree expansion forces a positive
boundary density. Thus varying the source graphings is essential;
searching only for better partitions of that fixed certificate fails
even in this known fixed-price family.

Section 6 explains its equivalence to factor-cost preservation in
the finitely generated setting. That equivalence is a reformulation,
not evidence that the premise is established.

Test the claim where fixed price is known (checked 2026-09-12 against
Gaboriau's lecture notes,
<https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf>,
version of 3 October 2025). Section 6 of the artifact shows that once
factor cost is preserved, a lifted near-optimal finite-label base graphing
gives K_n=0 with singleton blocks. So the claim holds for every finitely
generated group with fixed price. That includes amenable groups (Theorem
2.20 of the notes), free and surface groups (Corollaries 2.25 and 2.30),
SL_n(Z) for n>=3 (Corollary 2.44) and products with Z (Corollary 2.52). No
known case kills it, and the (r-1)/4 bound above for the fixed certificate
on F_r x C_M is not a counterexample. For a single group the claim is
equivalent to fixed price, so a new case needs a new fixed price theorem.
Two natural classes add none. For finite graphs of groups with amenable
edge groups, Corollaries 2.28 and 2.32 already give fixed price whenever
the vertex groups have it. For a free product A*B, Theorem 2.27 gives
C(a)=C(a|A)+C(a|B) for every free action, so the question reduces to A
and B.

Localize the obvious certificates: base-oblivious ones, including lifts
of graphings of a to a x b -> b. This dies at the weighted boundary
premise itself, for every partition and every block size. The
established `fpbs-relative-cycle-diagonal-absence-split` shows
<K delta_e,delta_e> >= (1-p_e) rho_H(e), where rho_H is the finite-cycle
weight. When occupancy ignores the base, H is Cayley, and an
infinite-order label crosses blocks on measure at least 1/M. The
established `fpbs-oblivious-certificates-never-localize` then gives
(1+2dM^2)Tr(P_out K) >= 2dM sum (1-p_s) rho_s. This is at least 2/3 for
torsion-free non-cyclic groups with beta_1=0 at cost below 4/3, so already
on Z^2, where fixed price holds. The invariant is the diffuse cycle
weight. Any construction of this premise must make boundary-edge
occupancy almost base-measurable, and it cannot come from
the forgotten factor's own near-optimal graphings. The retraction residual of
Section 7 is not covered by this obstruction. The artifact is
`research/artifacts/fpbs/docs/oblivious-occupancy-localization-obstruction.md`.

2026-09-17, second pass: localize fully supported, non-oblivious
certificates on nonamenable groups. This dies at the rounding rule of
Theorem 6.1 (tree per block, retain all crossing edges), for every
occupancy function. The established
`fpbs-retained-boundary-rounding-isoperimetric-floor` shows the output
cost is exactly 1 + eps_bd(H,E), with eps_bd the average over blocks of
sum_C (|boundary_H C|/2 - 1)/|B|. If the conditional support contains
a fully supported generating S_0, Mader's theorem and the Cheeger
constant give c(H') >= F_0 = 1 + (1/2 - 1/d_0) h(Gamma,S_0). So
(1+2dM^2)Tr(P_out K) >= F_0 - c(Phi) for all blocks. On F_2 x Z, which
has fixed price 1, F_0 >= 5/3. The invariant is the excess boundary
density of the conditional support. The M-free bound
c(H') <= c(Phi) + (crossing absence) + (interior disconnection), proved
there, fails in the same way. It escapes wave 4 on Z^2, but only by
re-proving amenable cost one.

Consequences. K is idle for this rounding: (14) implies the K-free (BF),
inf_E c(H'(H_n,E)) <= c(Phi_n) + o(1), which is itself equivalent to
preservation. A localizing sequence must make label occupancy vanish
exactly on base-measurable sets of positive measure. The retraction of
Section 7, which deletes crossing edges, is not covered. The artifact is
`research/artifacts/fpbs/docs/retained-boundary-isoperimetric-floor-2026-09-17.md`.
