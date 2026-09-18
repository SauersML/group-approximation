---
rg: 2
id: higman-four-cycle-intrinsic-mf-seed
kind: claim
title: Higman's four-cycle is the concrete intrinsic torsion-free MF-seed test
root: true
distinct_from:
  torsion-free-fp-ah-mf-radical-seed: that asks for any intrinsic seed; this fixes Higman's four-generator presentation and identifies the exact marked point-operator-norm statement still missing.
  map-matricial-stability-non-mf: that is a general implication from matricial stability and finite-dimensional sterility; here cyclic symmetry makes the one-mark statement exactly trivial-tuple stability for this finite presentation, so the candidate does not evade the stability problem but isolates it in four explicit relations.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that is a normalized-Hilbert--Schmidt reduction; this asks for operator-norm collapse and cannot consume HS-nearness of the four occurrences.
artifacts:
  - research/artifacts/higman-cycle-bs-stability-gate-2026-08-21.md
---

**OPEN.**  Let

```text
Hig=<g_0,g_1,g_2,g_3 |
     g_i g_(i+1) g_i^(-1)=g_(i+1)^2, i in Z/4Z>.       (HMF1)
```

Prove, without Property `(T)` or any Kazhdan input, that for every sequence
of finite-dimensional unitary tuples `(U_(0,n),...,U_(3,n))` satisfying

```text
max_i ||U_(i,n) U_(i+1,n) U_(i,n)^* - U_(i+1,n)^2|| -> 0
                                                               (HMF2)
```

in operator norm, one has

```text
||U_(0,n)-1|| -> 0.                                    (HMF3)
```

This is the exact marked point-operator-norm collapse needed for the
intrinsic seed.  Cyclic symmetry then gives `(HMF3)` for every generator;
finite presentation converts `(HMF2)--(HMF3)` into triviality of every
homomorphism from `Hig` to a norm matrix corona.  Hence

```text
Rad_MF(Hig)=Hig,                                       (HMF4)
```

and any nonidentity generator is a valid marked radical element.

## Why this is the narrow torsion-free candidate

The following are literature/background facts, not premises of a completed
no-literature endpoint in this repository:

- `Hig` is finitely presented, infinite, and torsion-free;
- `Hig` is acylindrically hyperbolic (Minasyan--Osin, Corollary 4.26; also
  recoverable from Martin's cubical action);
- Higman's no-finite-quotient theorem and Malcev residual finiteness for
  finitely generated linear groups imply that every exact finite-dimensional
  unitary representation of `Hig` is trivial.

Thus the group-theoretic shape required by
`torsion-free-fp-ah-mf-radical-seed` is already known for this one explicit
presentation.  But those facts, including torsion-freeness, nontriviality,
and acylindrical hyperbolicity, must be internalized before this node can be
a premise of the requested unconditional no-literature Lean endpoint.
Exact finite-dimensional sterility is only a calibration and does not imply
`(HMF3)`.

## The marked statement is already full trivial-tuple stability

For this cyclic presentation, `(HMF3)` is not materially weaker than
point-operator-norm stability.  Applying the same statement after cyclically
renaming the four generators makes every `U_i` converge to `1`; the trivial
tuple is then an exact representation.  Conversely, correction to exact
representations plus exact finite-dimensional sterility gives `(HMF3)`.

Equivalently, the sequential statement is the dimension-uniform modulus:
for every `epsilon>0` there is `delta>0` such that every finite-dimensional
tuple with relator defect below `delta` satisfies

```text
max_i ||U_i-1|| < epsilon.                            (HMF5)
```

Failure of this modulus supplies a counterexample sequence by choosing the
defect below `1/n` at one fixed positive distance; the converse is immediate.
Thus the desired implication is exactly stability of this presentation
toward its unique finite-dimensional representation, not merely a local
marked estimate.

## The four-seam gate

The established HS theorem
`higman-hs-microstates-are-near-glued-exact-bs-cycles` replaces each of the
four relations by an exact `BS(1,2)` packet and leaves four repeated-generator
seams.  It does not prove `(HMF3)`: normalized-HS closeness does not control
operator norm, and the known split clocks retain a four-matcher product
holonomy.

An operator-norm packet proof would have to establish both of the following
new statements, with dimension-independent moduli:

1. same-dimension operator-norm correction of an approximate `BS(1,2)` pair
   to an exact pair;
2. collapse of every cyclic family of four exact pairs whose four incoming
   and outgoing generator occurrences converge to one another in operator
   norm.

Even the first local statement is not available: Eilers--Shulman--Sorensen
explicitly leave operator-norm matricial stability of the metabelian groups
`BS(1,m)`, `m>1`, open.  Bypassing local correction is allowed, but it must
still prove the direct four-relation implication `(HMF2)=>(HMF3)`.

Consequently this node records a concrete candidate and an exact analytic
seam, not a solution.  Establishing it, together with internal proofs of the
background group facts, would provide the no-`(T)` input for the torsion-free
routing saturation theorem.

Two established calibrations narrow a possible countermodel further.
`one-small-higman-generator-collapses-the-four-cycle` shows that every
generator of a noncollapsing sequence must remain outside the operator-norm
`sqrt(2)` basin.  For the concrete `3^n` clocks,
`periodic-higman-clock-centralizer-has-linear-width` computes
`dim_C {P}'=2q-1`; the clock degeneracies therefore do not supply an
unrestricted quadratic-size gauge space for absorbing the fourth return.
The sharper `higman-fourth-return-jointly-centralizes-clock` observes that a
successful return `K^4` must almost commute with both `P` and `D`, whose exact
joint commutant is only `C^(n+1)`.  This still does not close the gate:
`periodic-clock-p-commutant-has-uniform-joint-gap` gives a dimension-free
correction once `K^4` commutes with `P` exactly, and a rate-dependent one when
`3^n r->0`, but the gate assumes only `r->0` and still lacks a compatible
fourth-root correction.  This rate loss is real at the almost-commutant
level: `periodic-clock-has-opnorm-almost-central-fourth-power-escape`
exhibits unitary fourth powers far from the joint commutant despite both
commutators vanishing.  What remains special, and open, is imposing the
matcher equation on that same fourth root.
On the other hand, `order-four-bs-matcher-builds-higman-opnorm-microstate`
shows that matchers with both vanishing one-step error and
`||K^4 P K^(-4)-P||->0` would immediately refute this node; no stronger return
`K^4->1` is required.

The one-step side can be sharpened further without changing the gate.
`primitive-shell-bs-clock-has-optimal-opnorm-matcher` restricts to the single
primitive `3^n`-root shell, where `{P,D}'` is scalar and the optimal matcher
error is `Theta(3^(-n))`.  Thus neither lower-shell multiplicities nor the
`O(n/3^n)` whole-clock matching loss is essential: the unresolved condition
is still exactly the fourth return of the primitive-shell matcher.
For the exact sorted spectral assignment,
`primitive-shell-sorted-matcher-is-one-phase-torus` reduces all matcher
freedom to `K=RH`, with one diagonal phase torus, and identifies the
parity-corrected doubling cocycle of the matched diagonal.  The resulting
phase optimization is explicit, but no analytic lower bound or vanishing
construction is currently known; nearby-spectrum mixing is also not covered.

## Attempts

- 2026-09-17, swarm-0917-w4-pull-pt-3 (inverter, numerical microstate
  census).  Result: `higman-opnorm-defect-profile-has-dim-twelve-witness`.
  The collapse modulus `(HMF5)` is equivalent to `lim_L m_c(L)>0`, where
  `m_c(L)` is a monotone profile (padding by `(+)1`).  An explicit tuple in
  `U(12)` has every generator at distance `>=1.985` from `1` and defect
  `0.3099`, so any threshold must satisfy `delta(1.98)<=0.31`.  Cycle-spectrum
  seeds satisfy `def>=2 sin(pi/L)`.  Riemannian descent on Schatten-`2m`
  surrogates plateaus at `def~0.31` for `L=12,28`.  At `L=36,54` it fails to
  reach the padded twelve-dimensional value.  The order-four matcher optimum
  (`q=81`) has actual defect `1.39`.  **Dead as a route:** local descent sees
  no decay and cannot give a lower bound on `m_c(L)`, so the census neither
  supports a countermodel nor proves collapse.
- **Numerical scout of `(SPT7)` and of general matchers (2026-09-17,
  census-computation).**  Script:
  `experiments/higman-matcher-2026-09-17/sorted_torus_fourth_return.py`.
  All numbers come from local optimization. They are upper bounds on the
  relevant infima, never lower bounds, so this is evidence, not a proof.
  - *Sorted torus.* I minimized the normalized-HS return
    `||K^4P-PK^4||_2/sqrt(L)` over `K=RH`, from random starts and
    quadratic-chirp starts. Best values found:
    - `n=2`: `0.766`.
    - `n=3`: `0.579`, operator norm `0.881`. Random starts and the best
      chirp `theta_a=2pi(3a^2/4+a/3)/L` both reach this value, so it is
      probably the global minimum.
    - `n=4`: `1.271`, operator norm about `2`. Here no start, chirp starts
      included, got below the value for a random unitary.

    The trend does not look like vanishing, but the `n=4` value may be
    local. The sorted torus does not visibly pay the fourth return.
  - *General matchers.* I ran Riemannian descent over all of `U(L)` on
    `lam*||KP-DK||_2^2+||K^4P-PK^4||_2^2`. At `lam=1` the return is almost
    paid (HS `0.036`--`0.042`, op `0.06`--`0.07` for `n=2,3,4`), but the
    optimizer gives up the matcher equation instead (`eps` op
    `0.89, 0.61, 0.52`). At `lam=30` the matcher error falls to op
    `0.28`/`0.32` and the return climbs back to op `0.47`/`1.23` at
    `n=3,4`. In dimensions `L<=54`, no matcher came near having both small
    `eps` and small `r` in operator norm. The trade-off does not visibly
    improve with `n`.
  - *Verdict.* No numerical sign of an operator-norm clock countermodel. The
    refutation lane through `(HOM5)` gets no support at `q<=81`. What remains
    open is an analytic lower bound on the `eps`/`r` trade-off, or larger-`q`
    evidence.
- **2026-09-17, swarm-0917-w5-pull-pt-1 (obstruction-miner, cohomology-index).**
  Result: `higman-cohomological-countermodel-invariants-vanish` (established).
  I tried to refute `(HMF3)` with an index-type countermodel, in the style of
  Voiculescu, Exel--Loring, Dadarlat almost-flat K-theory, delocalized
  Dadarlat, or the Dadarlat--Glebe obstruction class.
  - **The lane is empty.**  The cellular boundary of every cycle
    `H_k(BS(1,m))` is `(1-m)` times a cyclic permutation.  So
    `H_2 = 0` by Hopf and `H^2(Gamma;V) = 0` for every vector space `V`.
    For `Hig`, Baumslag--Dyer--Heller give a classifying 2-complex and
    acyclicity, and the group is torsion-free.
  - **Where it dies.**  Every member dies at the pairing step: the invariant
    lives in a zero group, or in the rank summand of `K^0(BHig) = Z`.
  - **Consequence for countermodels.**  Any operator-norm countermodel to
    `(HMF3)` is cohomologically invisible.  The surviving refutation lanes
    are non-index ones (amenable or MF-representable quotients, spectral
    clocks).
  - **Scope.**  This is not a proof of `(HMF3)`, since `H^2 = 0` supplies no
    perturbation theorem.  The success of the same lane on
    `SL_4(F_q[t^(+-1)])` depended on torsion, which `Hig` lacks.
- **2026-09-18, swarm-0917-w6-w6-ptm-pull (reframing).**
  Results: `higman-seam-gate-needs-only-padded-bs-correction` (established,
  elementary) and `bs1n-rq-padded-opnorm-stability` (established, imported).
  I also opened the route `higman-collapse-via-trivially-padded-bs-correction`.
  - **Statement 1 of the gate is not needed.**  Same-dimension correction of
    approximate `BS(1,2)` pairs is the open Eilers--Shulman--Sorensen question.
    It can be replaced by correction after block sum with an identity block,
    `bs12-trivially-padded-opnorm-correction`.  That statement together with the
    glued exact-cycle collapse `higman-exact-packet-cycles-collapse-opnorm`
    implies `(HMF5)`.  Conversely, `(HMF5)` implies that collapse.
  - **Published padded stability does not close it.**  Willett arXiv:2408.13350,
    Theorem 7.9 and Example 7.11, gives operator-norm `R_q`-stability of
    `BS(1,n)`.  The auxiliary summand there is an uncontrolled finite-quotient
    representation.
  - **Class killed.**  Per-seam padded corrections with uncontrolled
    auxiliaries die when the auxiliary summands of different seams are glued.
    Exactly glued auxiliaries are trivial, by a smallest-prime chain on odd
    orders.  Approximately glued auxiliaries are themselves a collapse input.
    So such methods reach the gate only through trivially padded instances.
  - **Bounded-order collapse.**  The quantitative prime chain proves collapse
    for exact-packet cycles with `o_i o_(i+1) eta < 2`.  It dies on fine clocks
    with orders `>= eta^(-1/2)`.
