---
rg: 2
id: fpbs-q-normal-hyperfinite-chain-forces-cost-one
kind: claim
title: A measured q-normalizer chain from an aperiodic hyperfinite subrelation to the orbit relation forces cost one
distinct_from:
  fpbs-wq-normal-price-one-subgroup-forces-price-one: that is the group-level statement for an infinite wq-normal subgroup of fixed price one; this is per action and starts from an arbitrary aperiodic hyperfinite subrelation, not necessarily the orbit relation of any subgroup, with q-normality measured by aperiodicity of T cap T^g.
  fpbs-relative-traffic-descent-over-hyperfinite-spine: that lets routing plans use a cost-one hyperfinite spine for free and keeps the relative budget C-1; this names a structural property of the spine (its measured q-normalizer chain reaches R) under which the relative budget is zero.
  fpbs-cost-one-backbone-fixes-completion-bill: that shows the completion bill over any cost-one backbone is C(R)-1; this gives a sufficient condition for that bill to vanish.
---

**OPEN** (demoted 2026-09-17 at landing: referee lens 2 of three refuted the
Consequences section on import scope; see Attempts). Let `Gamma` be a countably infinite
group acting freely and p.m.p. on `(X,mu)`, with orbit relation `R`. For a
Borel subrelation `T <= R` and `g in Gamma` put

    T^g = {(x,y) : (gx,gy) in T},
    QN(T) = {g in Gamma : T cap T^g is aperiodic}.

Here aperiodic means almost every class is infinite. Start from an aperiodic
hyperfinite `T_0 <= R` and set `T_(k+1) = T_k v R_(H_k)`, where
`H_k = <QN(T_k)>` and `v` denotes the generated relation. If
`union_k T_k = R` almost everywhere, then `C(R)=1`.

**Consequences.**

* The same proof works for a chain indexed by any countable ordinal, with
  unions at limit stages. `QN` is monotone: `T <= T'` gives
  `T cap T^g <= T' cap T'^g`.
* If this holds for the Bernoulli action, `Gamma` has fixed price one, by
  `fpbs-bernoulli-maximal-cost`. In every case `beta_1^(2)(Gamma)=0`, by
  `fpbs-amen2-betti-cost-input`. So groups with `beta_1^(2)>0`, such as free
  and surface groups, have no such chain in any free action.
* **Recovery of the subgroup mechanism.** Freeness gives
  `R_H cap (R_H)^g = R_(H cap g^(-1) H g)`. So for infinite amenable `H`,
  `QN(R_H)` is the set of `g` with `H cap g^(-1)Hg` infinite, and the chain is
  the wq-normal hull. This recovers the amenable case of
  `fpbs-wq-normal-price-one-subgroup-forces-price-one`.
* The routing of Section 8 of
  `research/artifacts/fpbs/docs/cost-cycle-structure.md` on `F_r x Z` is the
  one-step normal case. There `T_0` is the orbit relation of the central `Z`,
  so `T_0^g=T_0` for every `g` and `QN(T_0)=Gamma`.
* The hyperfiniteness of `T_0` matters. For any aperiodic `T`, the subrelation
  `R` itself has `QN(R)=Gamma`, so the content lies in reaching `R` from a
  cost-one hyperfinite start.

**Proof.** See `fpbs-q-normal-hyperfinite-chain-forces-cost-one-proof`.

## Attempts

**Written proof by small complete sections of `T cap T^g` (2026-09-17;
refereed, one refutation).** The route
`fpbs-q-normal-hyperfinite-chain-forces-cost-one-proof` compiled this claim
ESTABLISHED. Three referee lenses checked it. Lenses 1 and 3 found no gap. Lens
2 returned refuted=true. It found the main lemma `C(R)=1` sound, including the
marker-lemma step, the path `y ~ x -> gx ~ gy`, the transfinite limit stages and
the `beta_1^(2)=0` consequence. What it refuted is the fixed-price-one
consequence. That consequence is stated for arbitrary countably infinite
`Gamma`, but `fpbs-bernoulli-maximal-cost` only covers "every infinite finitely
generated group Gamma" (Abert--Weiss / Kechris weak containment). No import in
the graph covers infinitely generated `Gamma`. Lens 2 also noted a small
arithmetic slip: the weights `delta 2^(-k-j)` with `k>=0`, `j>=1` sum to
`2 delta`, so the bound is `1+3 delta`, not `1+2 delta`. The slip is harmless
and is now corrected in the route. Proposed fix: restrict the fixed-price
consequence to finitely generated `Gamma`, or import Bernoulli maximal cost for
all countable groups. The route now requires the OPEN gap claim
`fpbs-q-normal-chain-fixed-price-consequence-scope`, so this claim derives OPEN
until that gap is closed and the route is refereed again.
