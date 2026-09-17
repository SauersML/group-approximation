---
rg: 2
id: fpbs-benjamini-schramm-counterexample-exists
kind: claim
title: Some nonamenable Cayley graph has coinciding percolation thresholds
root: true
distinct_from:
  fpbs-fixed-price-one-percolation-kernel: that is the positive statement for nonamenable fixed-price-one groups, the last case of the cost route; this is the negation of the universal goal, and by Lyons any witness for it must lie inside that same class.
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/spectral-spike.md
  - research/artifacts/fpbs/exploration.md
---

**OPEN; the negation of `fpbs-benjamini-schramm-universal`.** There exist a
nonamenable finitely generated group `Gamma` and a finite symmetric generating
set `S` with

```text
p_c(Cay(Gamma,S)) = p_u(Cay(Gamma,S)).
```

This node exists because of the graph's refutation convention. A
counterexample is not a route into the universal goal; it is an ESTABLISHED
negation claim, and only when this claim is established does
`fpbs-benjamini-schramm-universal` acquire
`refuted_by: [fpbs-benjamini-schramm-counterexample-exists]`.

**The witness class is pinned down.** By Lyons, arXiv:1109.5418, a finitely
generated group without fixed price one has a nonuniqueness phase on every one
of its Cayley graphs. So any witness here is a nonamenable group **of fixed
price one**: it satisfies the Fixed Price assertion for its own group rather
than contradicting it, and it lies inside
`fpbs-fixed-price-one-percolation-kernel`. Section 5 of the forwarded
2026-09-09 priority assessment draws the operational consequence: proving
fixed price one for one more nonamenable group does not advance the
percolation problem, it only moves the group into the class where the cost
obstruction is silent.

It must also avoid every established positive case:
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness` (nonamenable Gromov
hyperbolic quasi-transitive graphs, and graphs with a nonunimodular
quasi-transitive automorphism subgroup) and `fpbs-sc-choi-seo` (every Cayley
graph of an acylindrically hyperbolic group). It must fail Hutchcroft's L2
boundedness conjecture `fpbs-nonamenability-bounds-critical-connectivity-operator`,
so establishing this claim would refute that conjecture too.

## Attempts

* **Show the collapse scenario is internally consistent** (response 9,
  `spectral-spike.md` Sections 4--7). Assuming `p_c=p_u=c`, the note derives
  what collapse forces: a spectral atom of mass `theta(p)^2` at `1` appearing
  immediately above `c`, and conditional pivotal counts of order
  `n exp(alpha n)` for every `alpha<lambda_0/2`. Section 7 then exhibits a
  monotone FIID partition model on the same nonamenable graph that realizes
  exactly this spectral jump, with explicit finite-`n` formulas and a
  logarithmic-derivative peak of rate precisely `lambda_0/2`. **Why this is
  not a counterexample:** Section 7 says so in its own terms. The partition
  classes are not clusters of the ambient Cayley graph. For every `t` in
  `(0,1)` a selected vertex has all `d` neighbours unselected with probability
  `t(1-t)^d>0`, and ergodicity produces such isolated vertices almost surely;
  they belong to the unique infinite class but are not connected to it through
  edges of the graph. The toy parameter also has threshold zero rather than
  `c>0`, so identifying its logarithmic derivative with a Bernoulli pivotal
  count is an error the note names explicitly.
* **Build a nonamenable graph with no indispensable edges** (response 4,
  `creative-branches.md` Section 1.3; response 8, `exploration.md` Section 1).
  The model `H_epsilon` on `T_{2r} x Z` keeps all vertical edges and each
  horizontal edge with probability `epsilon`; it is connected, bridgeless, and
  has divergent mean replacement-route length. **Where it dies:** it is a
  dependent anisotropic law, not Bernoulli percolation on a Cayley graph, and
  Proposition 1 of `exploration.md` shows it is collectively fragile,
  `p_c(H_epsilon) -> 1` as `epsilon` decreases. It separates route length from
  pivotality; it does not produce coinciding thresholds anywhere.
* **Use a cost-one group directly.** Every group in the archive's
  fixed-price-one families (`fpbs-amen2-fixed-price-one`,
  `fpbs-bounded-exponent-two-groups-fixed-price`, `fpbs-sc-fixed-price-family`,
  `fpbs-tfl-fixed-price`) is admissible as a candidate by the Lyons
  constraint. **Where it dies:** admissibility is not a threshold
  computation. For the explicit small-cancellation family the opposite is
  proved, `fpbs-sc-percolation-family` and `fpbs-ew-window` give an actual
  nonuniqueness interval; and the quantitative cost bound of response 1
  degenerates to `0 <= 0` under threshold equality, so it neither forbids nor
  produces a collapse. No candidate has a proved upper bound on `p_u` matching
  a lower bound on `p_c`.
* **Reasoning from the two endpoint facts.** Absence of an infinite cluster at
  `p_c` and absence of a unique cluster at `p_u` are both known and both
  remain true when `p_c=p_u`. Section 8 of `spectral-spike.md` records this
  after a literature check: no implication about strictness may be inferred by
  combining them.
* **Kazhdan projection applied to the two-point function** (sw-029,
  2026-09-17, inverter lane). Assume a witness `Gamma` has property (T), with
  Kazhdan constant `kappa` for `S`. Then `phi_p(x)=tau_p(o,x)` is a normalized
  positive definite function on `Gamma`: its GNS vector is `e_{C(o)}` in
  `L^2(P; l^2(clusters))`. Its invariant mean is
  `W(p)=M(phi_p)=||P_inv xi||^2`. By ergodicity, indistinguishability of
  infinite clusters and the Alaoglu--Birkhoff mean ergodic theorem,
  `W(p)=theta(p)^2 1{uniqueness at p}`. Under (T), `W(p)=s_p(p_0)`, where `p_0`
  is the Kazhdan projection in `C*(Gamma)` and `s_p` is the state defined by
  `phi_p`. Since `phi_p` is pointwise left-continuous in `p`, `W` is
  left-continuous. This yields two things. (a) Either `p_c=p_u`, or there is
  no uniqueness at `p_u`. (b) The quantitative bound
  `1-W(p) <= 2(1-p)/kappa^2`, so `p_u <= 1-kappa^2/2`. Calibration: planar
  hyperbolic surface groups have uniqueness at `p_u`, and they lack (T), as
  they must. **Where it dies:** (a) is the Lyons--Schramm conclusion for
  Kazhdan groups, and `fpbs-pu-nonuniqueness-cannot-separate` already shows
  that no endpoint statement of the form "no unique cluster at `p_u`" can force
  strictness. The exact failing step is the continuity of `W` at `p_c` under
  collapse. For a unimodular nonamenable transitive graph `theta(p_c)=0`
  (BLPS), and `theta` is right-continuous, so `W(p)=theta(p)^2 -> 0 = W(p_c)`
  as `p` decreases to `p_c`. Thus `W` is continuous at `p_c`, and the
  one-sided continuity supplied by the Kazhdan projection has nothing to
  contradict. The same computation gives `M=theta^2 1{U}` for the invariant
  mean of any positive definite function `P(o ~ x)` built from an ergodic
  invariant random partition with indistinguishable infinite classes, sprinkled
  couplings `C_q(o)` included. So the whole class "invariant means,
  equivalently Kazhdan projections, of cluster two-point functions" is silent
  on collapse. A contradiction would have to come from a non-mean
  functional, one that sees `tau_p` outside the trivial isotypic component,
  such as the spectral mass of `phi_p` near but not at the trivial
  representation.
* **Spectral mass near but not at the trivial representation, for Kazhdan
  groups** (sw-128, `fpbs-kazhdan-spectral-data-realized-by-fiid-collapse`).
  **Dead, as a class-killing obstruction.** Take any factor-of-iid percolation
  with at most one infinite cluster, which under collapse includes every
  Bernoulli `xi_p`. Give each finite cluster a random sign. Then the two-point
  state is `theta^2 epsilon + sigma` with `sigma` reduced, because the
  Bernoulli Koopman representation is contained in a multiple of `lambda`.
  So under collapse the state has no mass near `1` other than the atom. The
  non-atomic part is isolated by the Kesten gap for every nonamenable group,
  and property (T) adds nothing to it.

  The profile is also realized. On `p^-1(Sp_2n(Z)) ⊂ Sp_2n(R)~` (Kazhdan) there
  are FIID sparse spines built from Bernoulli-thinned crosses in central-`Z^2`
  cosets, linked along whole central lines
  (`fpbs-central-z2-groups-have-fiid-sparse-spines`, which settles
  `fpbs-kazhdan-sparse-spines` for these groups). They feed an FIID collapse
  family equal to Bernoulli through `p_c`, weak-* continuous at `p_c`, that
  realizes the Kazhdan projection values, the reduced non-atomic part, the
  walk-sampling measures and Hutchcroft's bound.

  Exact failing steps:
  * (F1) The non-trivial part does not carry the transition. It is reduced and
    continuous, and only the continuous atom moves.
  * (F2) Hutchcroft's bound is compatible with collapse: through
    Cowling–Haagerup–Howe it makes `s_(p_c)` reduced.
  * (F3) The only discriminating input is Russo's identity, or more generally
    independent increments above `p_c`, used by the pivotal-spike theorem. A
    proof must be quantitative in those increments, not representation
    theoretic.
