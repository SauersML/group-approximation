---
rg: 2
id: fpbs-fiid-soft-collapse-iff-fiid-sparse-spines-proof
kind: route
title: Read a spine off the unique cluster, transport it between generating sets along words, and check that the invariant collapse construction stays a factor of iid
target: fpbs-fiid-soft-collapse-iff-fiid-sparse-spines
requires:
  - fpbs-soft-collapse-iff-invariant-sparse-spines
  - fpbs-critical-no-infinite-cluster
  - fpbs-cluster-count-trichotomy
  - fpbs-sparse-spine-cost-bound
  - fpbs-bernoulli-maximal-cost
  - fpbs-sheet-spines-not-weakly-contained-in-bernoulli
---

**Audit note (2026-09-17).** Referee lens 1 refuted the second bullet of
Proposition F in the atomic case: the conclusion "not strongly ergodic" does
not follow, since a `Gamma`-action on `Z/r` is strongly ergodic. The route
now takes the corrected bullet as the open prerequisite
`fpbs-sheet-spines-not-weakly-contained-in-bernoulli`. Referee lens 3 refuted
the closing sentence of the target that no group with FIID sparse spines is
known (counterexample on `F_2 x Z^2`). The referees found (i)--(iii) and
Corollary D sound. The argument below is kept as the attempt.

Notation as in the target. "The invariant proof" means
`fpbs-soft-collapse-iff-invariant-sparse-spines-proof`, which proves the
established Theorem A of `fpbs-soft-collapse-iff-invariant-sparse-spines`.

## (i) Threshold equality gives FIID spines

Let `p_c = p_u` and `t > p_c`. By `fpbs-cluster-count-trichotomy` (simultaneous
uniqueness), `xi_t` has exactly one infinite cluster `I_t` a.s. Off a null
set, `I_t` is the union of all infinite clusters: its vertices are those in
`∩_R {x <-> ∂B_R(x)}` and its edges are the open edges between them. This is a
measurable function of `U`, and relabelling by `g` moves it to `g I_t`. Hence
`I_t` is an FIID random subgraph, a.s. connected and infinite.

Its density is `theta(t) = lim_R P_t(o <-> ∂B_R)`. This is a decreasing limit
of polynomials in `t`, each nondecreasing, so `theta` is nondecreasing and
upper semicontinuous, hence right-continuous. By
`fpbs-critical-no-infinite-cluster`, `theta(p_c) = 0`. So `theta(t) -> 0` as
`t ↓ p_c`, and the graphs `I_t` are FIID sparse spines. ∎

## (ii) Independence of the generating set

Let `S'` be another finite symmetric generating set. For each `s in S`, fix an
`S'`-word `w_s` with value `s`. For a word `w = s_1...s_l`, write
`P(x,w)` for the path `x, x s_1, ..., x s_1...s_l`; left multiplication maps
`P(x,w)` to `P(gx,w)`.

Given an FIID spine `L` in `Cay(Gamma,S)` of density `theta`, put
`L' = ∪ {P(x,w_s) : {x,xs} in E(L)}`.

* *Equivariance.* `L'` is an equivariant measurable function of `L`, so it is
  FIID.
* *Connectivity.* `L'` is connected and infinite, because it contains
  `V(L)` and joins the endpoints of every edge of `L`.
* *Density.* If `o in V(L')`, then `o = x u` for some `x in V(L)`, some `s`
  and some prefix `u` of `w_s`. For fixed `(s,u)`, the vertex `x = o u^-1` is
  determined, so
  `P(o in V(L')) <= sum_s (|w_s|+1) theta`.

The same argument runs in the other direction. ∎

## (iii) FIID collapse families iff FIID spines

*Only if.* Given an FIID soft collapse family, (S4) and the argument of (i)
make the unique infinite cluster of `omega_t` an FIID spine of density
`theta(t) -> 0`.

*If.* Run Steps 1--4 of the invariant proof with FIID inputs.

* Take the spines `L_k` from independent iid fields, one for each `k`.
* Take the labels `lambda^k`, the tie-breaking labels and `U` from further
  independent fields.

Countably many independent iid uniform fields on `V ⊔ E` form one iid field
with base `[0,1]^N`, which is isomorphic to `[0,1]`. In Step 2, the distance
`r_k(x)`, the success event and the geodesic chosen by minimal tie-breaking
label are equivariant measurable functions of these fields. Hence
`Omega_n = ∪_{k>=n}(L_k ∪ C_k)` and every `omega_t` are FIID, jointly in `t` and
together with `U`.

The proofs of (S1), (S2), insertion tolerance and (S4) in the invariant proof
use only a.s. properties and independence, so they apply verbatim. Ergodicity
(S3) needs no ergodic decomposition. A factor of a Bernoulli shift of an
infinite group is mixing, hence ergodic. ∎

## Corollary D

The first statement is the contrapositive of (i), with (ii) used to pass from
one generating set to all of them.

For the second, take an FIID spine of density `theta` and pass to its vertex
set `I = V(L)`. The induced subgraph on `I` contains `L`, so it is connected.
`fpbs-sparse-spine-cost-bound` gives `C^*(Gamma) <= 1 + (d/2-1) theta` for
every `theta > 0`, so `C^*(Gamma) <= 1`. By `fpbs-bernoulli-maximal-cost`,
every free p.m.p. action has cost in `[1, C^*(Gamma)] = {1}`. ∎

## Corollary E

The listed properties are standard for factors of Bernoulli shifts.

* *Koopman representation.* `L^2_0` of a Bernoulli shift over a countable
  `Gamma`-set with finite stabilizers decomposes into quasi-regular
  representations on finite subsets, so it is contained in `infinity · lambda`.
  A factor gives a subrepresentation.
* *Strong ergodicity.* This passes from the shift to its factors, and Bernoulli
  shifts of nonamenable groups are strongly ergodic.
* *Cost.* A free extension of an FIID family that is itself FIID is a factor of
  a Bernoulli shift and so has cost at least that of the shift.

An argument of the stated form proves `p_u(omega) > p_c` for every family
satisfying its hypotheses. The family of (iii) satisfies them and has a unique
infinite cluster for every `t > p_c`, so the argument cannot be valid on a
group with FIID sparse spines. ∎

## Proposition F

*First bullet.* `N = ker pi` is infinite, since `Gamma` is nonamenable and `Z`
is amenable. `H` is a measurable function of the iid field with `H(n·) = H`
for `n in N`. An infinite group acts mixingly, hence ergodically, on its
Bernoulli shift. The shift of `Gamma` restricted to `N` is a Bernoulli shift of
`N` over the `N`-set `V ⊔ E`, whose stabilizers have order at most `2` and
whose orbits are therefore infinite. Such a shift is mixing, so `N`-invariant
functions are a.s. constant. So `H` is a.s. constant, equal to some fixed `H_0`
with `H_0 + pi(g) = H_0` for all `g`. Therefore `H_0 in {∅, Z}`.

*Second bullet.* Let `Ĥ = {h : pi^-1(h) ⊆ V(L)}`. It is a factor on which
`Gamma` acts by translation through `pi`. Suppose the system is weakly
contained in Bernoulli.

* It is then ergodic, so `P(Ĥ in {∅,Z}) in {0,1}`. That probability is `0`,
  because `Ĥ ≠ ∅` a.s. and `P(Ĥ = Z) <= P(o in V(L)) < 1`.
* If the law of `Ĥ` has an atom, ergodicity puts `Ĥ` on a finite orbit of a
  set of period `r >= 2`. Then the finite-index subgroup `pi^-1(rZ)` has a
  nontrivial invariant set.
* If the law has no atom, the Rokhlin lemma for the aperiodic translation
  gives almost-invariant sets. Every generator acts by a translation of length
  at most `max_s |pi(s)|`, so these sets are almost invariant under `Gamma`.

In both cases the system is not strongly ergodic for a nonamenable group.
Weak containment carries almost-invariant partitions down to the Bernoulli
shift, which is strongly ergodic (restricted to `pi^-1(rZ)` in the atomic
case). That is a contradiction.

For the sheet spines of Theorem B, `Ĥ` contains the Bernoulli height set
`H_k`, so `Ĥ ≠ ∅`. ∎

*Imported standard facts in Corollary E and Proposition F.* These are mixing
of Bernoulli shifts; strong ergodicity of Bernoulli shifts of nonamenable
groups (Losert--Rindler, Jones--Schmidt); downward preservation of almost
invariant sets under Kechris weak containment, which follows from its
definition; and Rokhlin's lemma for `Z`. Parts (i)--(iii) and Corollary D use
only the required nodes.
