---
rg: 2
id: sl-m-q-passes-to-finite-index-and-commutator-cores-proof
kind: route
title: SL_m(Q) is perfect with only central proper normal subgroups; finite-index subgroups of finitely presented groups are finitely presented
target: sl-m-q-passes-to-finite-index-and-commutator-cores
requires:
  - gl-n-q-targets-are-cofinal-in-n
  - fp-groups-with-a-locally-moving-simple-subgroup-are-isolated
  - germ-extension-base-trivial-characters-lie-in-sigma
---

Notation as in the target. `Z` denotes the centre of `SL_m(Q)`, the scalars `λI` with
`λ ∈ Q`, `λ^m = 1`; so `Z = {±I}` for `m` even and `Z = {I}` for `m` odd.

**Classical input (not re-proved).** For a field `K` and `m >= 2` with
`(m, |K|) ≠ (2,2), (2,3)`, the group `SL_m(K)` is perfect and `PSL_m(K) = SL_m(K)/Z` is
simple (Jordan–Dickson; e.g. Lang, *Algebra*, XIII §8, Theorems 8.3 and 8.4). Here
`K = Q` is infinite.

**Normal subgroups.** Let `N ⊴ SL_m(Q)`. Then `NZ/Z` is normal in the simple group
`PSL_m(Q)`, so `N <= Z` or `NZ = SL_m(Q)`. In the second case `SL_m(Q)/N ≅ Z/(Z ∩ N)` is
abelian, so `N` contains `[SL_m(Q), SL_m(Q)] = SL_m(Q)`. Hence every normal subgroup is
central or everything.

**Item 1.** Let `H <= SL_m(Q)` have finite index, with normal core `N` (the
intersection of the finitely many conjugates of `H`). Then `N` is normal of finite
index. `Z` is finite and `SL_m(Q)` is infinite, so `N` is not central, and
`N = SL_m(Q)`; hence `H = SL_m(Q)`. For `Γ_0 <= Γ` of finite index, `Γ_0 ∩ SL_m(Q)` has
finite index in `SL_m(Q)`, so it is `SL_m(Q)`.
For a divisible abelian `D`, every quotient of `D` is divisible, and a finite divisible
group is trivial. So `D` has no proper finite-index subgroup, and the same argument
applies.

**Item 2.** `SL_m(Q) = [SL_m(Q), SL_m(Q)] <= [Γ,Γ]`, and inductively
`SL_m(Q) = SL_m(Q)^(k) <= Γ^(k)`.

**Item 3.** A finite-index subgroup of a finitely presented group is finitely presented
(Reidemeister–Schreier). `M ∩ SL_m(Q) = SL_m(Q)` by item 1. The embedding
`g ↦ diag(g, det(g)^-1)` of `GL_(m-1)(Q)` into `SL_m(Q)` is recorded in
`gl-n-q-targets-are-cofinal-in-n`. For the monolith: item 3 of
`fp-groups-with-a-locally-moving-simple-subgroup-are-isolated` says `ncl_Γ(T)` is simple.

**Item 4.** `Γ′` is simple by the quoted Theorem 1.3 (verbatim text in
`research/artifacts/gq-gq-lit-hosts.md` §1, read from arXiv:2407.03149).
`SL_m(Q) <= Γ′` by item 2. Finite presentation:
- If `Γ/Γ′` is finite, use Reidemeister–Schreier as in item 3.
- If every nonzero character lies in `Σ^2(Γ)`: `Γ′` is the normal subgroup with abelian
  quotient whose associated character sphere is all of `S(Γ)`, and the Bieri–Renz
  criterion used in `germ-extension-base-trivial-characters-lie-in-sigma` gives type
  `F_2`.
- Under the four hypotheses of that node with `m = 2`: `B` perfect gives `B = [B,B] <= Γ′`
  and `Γ/Γ′` is abelian, so its Corollary gives that `Γ′` has type `F_2`, that is,
  `Γ′` is finitely presented.

**Calibration remark.** Germ groups of standard `V` are trivial at points that are not
eventually periodic and cyclic at eventually periodic points. A prefix replacement `α ↦ β` fixing `p = αx = βx` with `|α| ≠ |β|`
forces `p` to be eventually periodic; with `|α| = |β|` it forces `α = β`. So a germ group
that is a finite extension of one of these is virtually cyclic, hence residually finite,
hence contains no nontrivial divisible subgroup.
