---
rg: 2
id: co-sofic-irs-carry-no-strict-design
kind: claim
title: A co-sofic invariant random subgroup of a free group carries no strict automaton design, with a linear forward-to-reverse error bound
distinct_from:
  weakly-sofic-groups-are-surjunctive: that is surjunctivity of a group through approximation of its Cayley graph; this is the unimodular-network version, where forward and reverse tables vary from site to site and a quantitative inequality between their error densities passes to weak-* limits of finite Schreier graphs.
  separating-repetitive-amenable-schreier-families-force-soficity: that concerns fixed configurations on one amenable coset space of a group; this concerns designs carried by invariant random subgroups of a free group, with no group host and no amenability.
  surjunctive-groups-are-uniformly-quantitatively-surjunctive: that is a uniform quantitative form over a surjunctive group; this bounds the reverse-bad density by a constant times the forward-bad density over every finite Schreier graph, which is what lets site-varying tables pass to limits.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
  - research/artifacts/co-sofic-irs-carry-no-strict-design-proof-attempt-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts). It is not established because two referee
lenses refuted the stated inequality as written: `r` is used both for the rank of `F_r` and for
`R_tau + R_sigma`, so the literal constant is too small.

Let `D = (tau, sigma)` be a design of shape-dependent automata on Schreier graphs of `F_r`, with
alphabet `A` and radii `R_tau`, `R_sigma`. Put `r = R_tau + R_sigma`. Let `d_k` be the size of
the radius-`k` ball of the `2r`-regular tree. For an IRS `mu`, let `eps_D(mu)` be the probability
that the root is forward-bad, and `delta_D(mu)` the probability that it is reverse-bad (artifact
Section 2).

**Theorem.** Every co-sofic IRS `mu`, i.e. every weak-* limit of IRS of finite `F_r`-sets, satisfies

    delta_D(mu) <= ( d_(R_tau) + d_(2r) |A|^(d_r) ln|A| ) eps_D(mu).

In particular no co-sofic IRS carries a strict design, since a strict design has `eps = 0 < delta`.

- The inequality defines a closed convex set of IRS.
- On a vertex-transitive index set `eps` is `0` or `1`, so the inequality has content only once
  homogeneity is dropped.
- For normal `N`, `delta_N` is co-sofic iff `F_r/N` is sofic. With
  `atomic-irs-strict-designs-are-nonsurjunctive-quotients` this recovers Gromov-Weiss for finitely
  generated sofic groups.

Drafted proof: artifact Section 4.

## Attempts

1. **Count image patterns on a finite Schreier graph with forward-bad and reverse-bad sites, then pass to the
   limit (2026-09-17).** Formerly the route `co-sofic-irs-carry-no-strict-design-proof` (requires []); see
   `research/artifacts/co-sofic-irs-carry-no-strict-design-proof-attempt-2026-09-17.md` and Section 4 of
   `research/artifacts/irs-surjunctivity-heretic-2026-09-17.md`. Demoted on 2026-09-17 after the referee audit.
   Both lenses found proof steps 1-5 sound once `d_k` is the ball size in the `2*rank`-regular tree, so the
   qualitative conclusion (no co-sofic IRS carries a strict design) is expected to survive a restatement with a
   separate rank variable. Refutation reasons, verbatim:

   Referee lens 1 (refuted):

   > The claim fails as written because the constant C_D is defined wrongly. It uses the symbol r for two different things. In research/co-sofic-irs-carry-no-strict-design.md the statement says "Put r = R_tau + R_sigma. Let d_k be the size of the radius-k ball of the 2r-regular tree", while the graphs are still "Schreier graphs of F_r". The artifact (research/artifacts/irs-surjunctivity-heretic-2026-09-17.md, Sections 2 and 4) has the same clash: first r is the rank of F_r, then r = R_tau + R_sigma, and both d_(2r) and B_r(v) use it. So d_k ends up counting a tree of degree 2(R_tau+R_sigma) instead of 2*rank.
   >
   > First step that does not follow: route step 2, "at most eps N d_(R_tau) reverse-bad vertices fail the hypothesis". The same problem hits step 3 (the greedy choice removes at most d_(2r) candidates, and |B_r(v)| <= d_r). These bounds need |B_k(v)| <= d_k, which only holds when d_k is the ball in the 2*rank-regular tree. When the rank is larger than R_tau + R_sigma, the ball bound fails.
   >
   > The inequality as stated is false. Counterexample (checked by hand, no script run):
   > - Group and alphabet: F_20, |A| = 2, R_tau = 0, R_sigma = 1, so r = 1. The stated d_k is then 2k+1 and C_D = 1 + 5*8*ln2 ≈ 28.73.
   > - tau: constant c at sites with an a_1-loop, identity elsewhere.
   > - sigma: at a site with no loop, return y_v if every neighbour with a loop has value c, and flip y_v otherwise. At a loop site, return y_v.
   > - Finite F_20-set X: m loop points s_j, each with 38 fresh neighbours given by 3-cycles for a_2..a_20. a_1 fixes the s_j and pairs off the remaining 38m points, so none of them has a loop.
   > - Result: the forward-bad sites are exactly the loop sites, so eps = 1/39. Every site is a loop site or next to one, and all of these are reverse-bad, so delta = 1 > 28.73 * eps.
   >
   > The rest of the argument does check out if d_k is the ball in the 2*rank-regular tree: the lower bound, the excluded patterns, the disjoint-ball count, ln(1-u) <= -u, and the passage to the limit through clopen shape events. So the qualitative consequence (no co-sofic IRS carries a strict design) survives. The quantitative theorem as stated does not, and neither the claim nor the route should count as ESTABLISHED until d_k is restated with its own rank variable. The route lists no prerequisites and no experiment script exists. The remark that delta_N is co-sofic iff F_r/N is sofic is standard and is not used. The verdict was posted on the bus as 5b0c327d.

   Referee lens 2 (refuted):

   > The mathematics survives, but the claim's stated inequality is false as written. The fault is in the STATEMENT, not in proof steps 1-5.
   >
   > The claim node (research/co-sofic-irs-carry-no-strict-design.md) first says "Put r = R_tau + R_sigma" and only then says "Let d_k be the size of the radius-k ball of the 2r-regular tree". Read literally, the tree has degree 2(R_tau+R_sigma), not 2*rank(F_r). The artifact defines d_k before it redefines r, so it means the rank. But the claim puts the definitions in the reverse order, and the proof node (research/co-sofic-irs-carry-no-strict-design-proof.md) never defines d_k at all. That leaves the literal constant too small.
   >
   > Counterexample to the literal statement:
   > - Setup: take F_20 with A={0,1}, R_tau=0 and R_sigma=1, so r=1 and the literal tree is 2-regular, giving d_0=1, d_1=3, d_2=5 and C'=1+5*8*ln2, about 28.73.
   > - tau: set tau x(v)=0 if v has an a_1-loop, and x(v) otherwise.
   > - sigma: set sigma y(v)=1-y(v) if some neighbour u of v has a loop and y(u)=1, and y(v) otherwise.
   > - The graph: a finite F_20-set of size N where a_1 has exactly one fixed point u, and the 38 points u.a_i^{+-1} (i>=2) are distinct and have no loops.
   > - Result: u is forward-bad (tau is constant there) and reverse-bad. Its 38 neighbours are forward-good, because y(u)=0 on the image, so sigma is the identity there. They are also reverse-bad, with witness p(u)=1, p(v)=0. Every other vertex is good and not reverse-bad.
   > - So eps=1/N and delta=39/N > 28.73 eps.
   >
   > Checks with d_k taken from the 2*rank-regular tree:
   > - Lower bound |tau(A^X)| >= |A|^((1-eps)N): holds.
   > - Excluded pattern: forward-good on B_(R_tau)(v) gives tau sigma y(v)=y(v), so y avoids p_v. Holds.
   > - Bad sites near X\G number at most eps N d_(R_tau): holds.
   > - Greedy 2r-separation gives |D'| >= |D|/d_(2r) with disjoint r-balls: holds.
   > - Product bound, then ln(1-u) <= -u, then the inequality: holds.
   > - Limit: shape events are clopen, so eps_D and delta_D are continuous affine and the inequality set is weak-* closed. Holds.
   > - The qualitative "no strict design" conclusion is correct.
   >
   > Calibration: the proof does use what separates the true case. It needs finite counting, which fails for the non-unimodular end-fixing tree, for monoids and for non-co-sofic IRS. The side remarks also check out: eps is 0 or 1 on a vertex-transitive graph, and delta_N is co-sofic iff F_r/N is sofic.
   >
   > Fix: rename R_tau+R_sigma to something like rho, and say that d_k is the ball size in the 2*rank-regular tree.
