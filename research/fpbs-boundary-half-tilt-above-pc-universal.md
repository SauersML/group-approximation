---
rg: 2
id: fpbs-boundary-half-tilt-above-pc-universal
kind: claim
title: On every nonamenable Cayley graph some quasi-invariant boundary with positive Radon-Nikodym growth has half-tilted susceptibility finite strictly above p_c
distinct_from:
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that is (K), one exponentially rare pair per radius; this is an l^1 bound on tau weighted by the positive-definite function phi_(1/2), which implies (K) with rate h/2 and is not implied by it a priori
  fpbs-two-point-some-lq-above-pc-universal: that is a finite l^q norm of tau for some q; this is a linear functional of tau weighted by a Koopman matrix coefficient, and it fails on every amenable Cayley graph for a structural reason (item 6 of the tilt claim) rather than through the l^q norm
  fpbs-hyperbolic-nonunimodular-critical-l2-gap: that is the strict gap p_c < p_(2->2) on two classes; this kernel sits below the l2 gap (it follows from p_c < p_(2->2) whenever a boundary with pi_nu weakly contained in the regular representation and positive Radon-Nikodym growth exists) and is asked on every nonamenable Cayley graph
  fpbs-boundary-tilted-susceptibility-kernel: that proves the framework, the implication to (K), the tree values and the amenable kill; this is the open universal statement the framework reduces to
  fpbs-stationary-boundary-half-tilt-dies-on-amenable-lamplighter: that kills stationary boundary inputs for [BT] on an amenable lamplighter and proves the ceiling p^nu_t <= exp(-h/2); this is the open universal statement
---

**OPEN ([BT]).** Let `G = Cay(Gamma,S)` be a Cayley graph of a finitely
generated nonamenable group. Then there are a standard Borel `Gamma`-space `Z`
and a quasi-invariant probability `nu` on it with the following two properties:

- `nu(h_nu > 0) > 0`;
- `p_c(G) < p^nu_t(G)`, that is, `chi^nu_(1/2)(p) < infinity` for some `p > p_c`.

The notation is that of `fpbs-boundary-tilted-susceptibility-kernel`.

**What it gives.** By item 3 of `fpbs-boundary-tilted-susceptibility-kernel`,
[BT] gives kernel (K) with `gamma >= h/2`, and hence `p_c < p_u`. The route is
`fpbs-worst-pair-rate-via-boundary-half-tilt`.

**Evidence and calibration.**

- *True on trees.* On `T_d` with the visual measure,
  `p^nu_t = (d-1)^(-1/2) > p_c` (item 5).
- *Below the l2 gap.* Item 4 gives `p_(2->2) <= p^nu_t` whenever
  `pi_nu ≺ lambda_Gamma`. So [BT] holds on every class with `p_c < p_(2->2)`
  for which such a boundary with positive Radon–Nikodym growth is available.
  - On hyperbolic groups, the Gromov boundary with a Patterson–Sullivan or
    harmonic measure is such a boundary (recalled, not imported).
  - For harmonic measure on any nonamenable group, weak containment comes from
    Zimmer-amenability of the Poisson boundary together with Kuhn's theorem, and
    positive growth comes from positive Avez entropy (recalled, not imported).
- *False on amenable groups.* Item 6 shows `p^nu_t = p_c` on every amenable
  Cayley graph with `gr > 1` and `p_c < 1`, for every boundary with positive
  Radon–Nikodym growth, even with a fully explicit boundary where every
  structural property is present. So any proof must use nonamenability of
  `Gamma`, or a property of `nu` that the Cauchy law on
  `BS(1,2) x Z` lacks, such as stationarity.

**Where it is hard.** The candidate class is groups where the gap is known only
through cost (Lyons' fixed-price-above-one groups), which have no hyperbolic or
nonunimodular structure. The natural candidate there is the Poisson boundary of
simple random walk. [BT] for it asks that the two-point function, weighted by
the Harish-Chandra-type function `phi_(1/2)(y) = <pi_nu(y)1,1>`, be summable
just above `p_c`.

## Attempts

1. **Transfer of Hutchcroft's nonunimodular proof (2026-09-18,
   swarm-0917-w9-w9-bs-follow; OPEN).**
   - *Idea.* Hutchcroft proves `p_c < p_c(lambda) <= p_t` for nonunimodular
     transitive groups (arXiv:1711.02590v3, Theorem pcpt). Items 1–2 of the
     tilt claim reproduce his structural inputs on boundary cocycles:
     - the tilted mass transport;
     - the duality `lambda <-> 1-lambda`;
     - log-convexity.
   - *Failure.* The transfer cannot use only these inputs. On `BS(1,2) x Z` with
     the Cauchy law they all hold, yet `p^nu_t = p_c`.
   - *Where it breaks.* A `zeta`-independent cocycle is trivial (rigidity
     remark). So the layers of `log Delta` move with the root. Hutchcroft's
     supermultiplicativity along layers would need bounds uniform over the orbit
     of `zeta`, while mass transport controls only `nu`-averages.
   - *What survives.* A transfer that also uses stationarity or harmonicity of
     `nu`, or a fibre-uniform estimate that fails for the Cauchy law, is not
     killed.

2. **Stationary boundaries (2026-09-18, swarm-0917-w10-w10-bs-last1; OPEN).**
   Established node:
   `fpbs-stationary-boundary-half-tilt-dies-on-amenable-lamplighter`.
   - *Kill.* On the amenable group `(Z/2 wr Z) x Z`, the limiting-lamp law of
     a drifted switch-walk-switch walk has all of the following:
     - it is `mu`-stationary, quasi-invariant, and the hitting law of the walk;
     - `Delta` is the Doob density;
     - `I(X_n;Phi)` grows linearly;
     - `nu(h_nu >= (log 2)/12) > 0`.

     Yet `p^nu_t = p_c`. So the survivor "stationarity or harmonicity of `nu`"
     from attempt 1 is removed. The class it removes is the Cauchy inputs plus
     stationarity, hitting law, linear information and the Doob density.
   - *Ceiling.* On every Cayley graph, `nu(h_nu >= h) > 0` implies
     `p^nu_t <= exp(-h/2)`, from `kappa_p(n) >= p^n`. This is sharp on `T_d`. So
     a witness of [BT] needs `h^*(nu) < 2 log(1/p_c)`. For stationary `nu`, the
     ceiling is bounded through `limsup I(X_n;Phi)/(L n)`.
   - *What survives.* A proof must use nonamenability of `Gamma` itself, for
     example `rho < 1` together with `pi_nu ≺ lambda` and a spectral gap
     estimate. Stationarity for a *symmetric* `mu` is not covered: on
     `Z/2 wr Z^3` the unfrozen window is not an interval.
