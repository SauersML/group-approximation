---
rg: 2
id: sl-m-q-passes-to-finite-index-and-commutator-cores
kind: claim
title: SL_m(Q) lies in every finite-index subgroup and every commutator subgroup of a host, so a finite-index simple monolith or a finitely presented simple G′ already carries GL_(m-1)(Q)
distinct_from:
  gl-n-q-targets-are-cofinal-in-n: that compares the inputs GL_n(Q), SL_n(Q), PGL_n(Q) across n; this says where SL_m(Q) must sit inside a given host, so that simplicity can be obtained from a subgroup of the host instead of the host itself.
  fp-groups-with-a-locally-moving-simple-subgroup-are-isolated: that proves the monolith ncl(T) of a locally moving host is simple; this adds that SL_m(Q) lies in it whenever it has finite index, and records the finite-presentation conditions under which the monolith or G′ is a finitely presented simple host.
  gl-n-q-embeds-in-fp-simple-group: that is the target; this is a reduction lemma that lets a construction stop at a host that is not itself simple.
artifacts:
  - research/artifacts/gq-gq-lit-hosts.md
  - research/artifacts/gq-gq-pp-simple-exits.md
---

**ESTABLISHED** by `sl-m-q-passes-to-finite-index-and-commutator-cores-proof`
(elementary; not independently reviewed; no novelty claimed).

## Statement

Let `m >= 2` and let `Γ` be a group containing `SL_m(Q)`.

1. **No finite quotients.** `SL_m(Q)` has no proper subgroup of finite index. So
   `SL_m(Q) <= Γ_0` for every finite-index subgroup `Γ_0 <= Γ`. The same holds for
   every divisible abelian subgroup of `Γ`, for example a copy of `(Q,+)`.
2. **Perfect.** `SL_m(Q)` is perfect, so `SL_m(Q) <= Γ^(k)` for every term of the
   derived series of `Γ`, in particular `SL_m(Q) <= [Γ,Γ]`.
3. **Finite-index simple subgroup.** If `Γ` is finitely presented and has a simple
   subgroup `M` of finite index, then `M` is finitely presented and simple, and
   `GL_(m-1)(Q) -> SL_m(Q) <= M`, `g ↦ diag(g, det(g)^-1)`. So the root
   `gl-n-q-embeds-in-fp-simple-group` holds for `n = m - 1`.
   - This applies to the monolith `M = ncl_Γ(T)` whenever `Γ` acts faithfully by
     homeomorphisms on a Hausdorff space and contains a simple `T` whose rigid
     stabilizers of nonempty open sets are nonabelian
     (`fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`, item 3). For
     example `Γ <= Homeo(C)` containing Thompson's `V`, with `T = V`: then `Γ` need not
     be simple; it is enough that `[Γ : ncl_Γ(V)] < ∞`.
4. **Commutator subgroup of a germ extension.** Let `Γ` be a finite germ extension of
   `B <= Homeo(X)` satisfying the hypotheses of Belk–Hyde–Matucci, arXiv:2407.03149,
   Theorem 1.3: "`B` is simple, locally moving, and has no global fixed points, and
   ... `B` and `G` have the same orbits in `X`", with conclusion "the commutator
   subgroup `G′` is simple". Then `SL_m(Q) <= Γ′` by item 2, and `Γ′` is a
   finitely presented simple host of `GL_(m-1)(Q)` as soon as `Γ′` is finitely
   presented. For `Γ` finitely presented, `Γ′` is finitely presented in each of
   these cases:
   - `Γ/Γ′` is finite;
   - every nonzero character of `Γ` lies in `Σ^2(Γ)` (Bieri–Renz, as used in
     `germ-extension-base-trivial-characters-lie-in-sigma`);
   - the four hypotheses of `germ-extension-base-trivial-characters-lie-in-sigma` hold
     with `m = 2` and `B` perfect. Every character of `Γ` then vanishes on `B`, so its
     Corollary applies with `N = Γ′ ⊇ B`.

## Reading for the swarm

- A host does not have to be simple. It is enough to reach a finitely presented `Γ`
  containing `SL_m(Q)` (any `m >= 3`) with one of three exits: a finite-index simple
  monolith (item 3); a finitely presented simple `Γ′` (item 4); or a type (A) action,
  which needs no simplicity at all (`fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg`).
- **Calibration of item 4.** Hypothesis 3 of
  `germ-extension-base-trivial-characters-lie-in-sigma` (finite-index germ groups)
  makes every germ group of `Γ` over `B = V` virtually cyclic or finite, because
  those of `V` are. Such germ groups contain no nontrivial divisible subgroup. So for
  hosts whose divisibility must live in large germ groups (O1, O3), the third bullet
  does not apply, and one of the first two conditions must be checked directly.

## Attempts

Proved; see the proof route.
