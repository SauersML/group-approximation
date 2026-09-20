---
rg: 2
id: automorphic-sofic-kazhdan-kernel-with-full-mf-radical
kind: claim
title: Some finitely generated torsion-free sofic Kazhdan group with full MF radical has an automorphism with a finite two-sided automorphic presentation
distinct_from:
  torsion-free-sofic-singly-generated-kazhdan-defect-core: that asks for a finitely presented full-radical core produced by a compression defect, which crosses Alekseev--Thom 6.1; this asks for a possibly infinitely presented kernel whose full radical may come from any mechanism, with the finiteness supplied by an automorphic presentation.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks for a kernel which may be MF and is saturated by an extrinsic defect of the mapping torus; this asks for a kernel with full MF radical in isolation, so the automorphism only supplies finite presentation.
  fp-sofic-kazhdan-group-not-residually-finite: that is Alekseev--Thom 6.1; a finitely presented instance of this claim answers it, but the claim is designed for infinitely presented kernels, which do not.
  mf-kazhdan-quotientless-mapping-torus-exact-radical: that is the extrinsic half (IO-ext) of the descent, with an MF kernel; this is the intrinsic half (IO-int), with a kernel that has no nontrivial MF quotient.
artifacts:
  - research/finite-outer-order-radical-witnesses-cross-alekseev-thom.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic.md
---

**OPEN.** There exist a finitely generated group `K` and `phi in Aut(K)` such that

```text
(P1) K is nontrivial, torsion-free, sofic and Kazhdan, and Rad_MF(K) = K;
(P2) K has a finite two-sided automorphic presentation (FAP1) for phi.
```

`exact-mf-radical-over-z-via-automorphic-full-radical-kernel` turns any such pair into a witness
of `torsion-free-sofic-exact-mf-radical-over-z`.

**Why this is the right branch.** By `finite-outer-order-radical-witnesses-cross-alekseev-thom`,
every witness of the goal either answers Alekseev--Thom 6.1 or lies in region (IO). There the kernel
is infinitely presented and `[phi]` has infinite order in `Out(K)`. Descent splits (IO) into
(IO-ext) and the present (IO-int). Here the radical of the mapping torus is **intrinsic**, so the
compression-defect obstructions do not apply: (IS), (NB), (BF), (GC) and (CI) in the extrinsic-kernel
node's Attempts 16 to 19 all concern defects created by the mapping torus. The price is (P1).

**Forced features.**
- If `K` in a solution is infinitely presented, as intended, then `[phi]` has infinite order in
  `Out(K)`. Otherwise a finite-index subgroup `K x Z` of the finitely presented mapping torus would
  make `K` finitely presented.
- `K` has no nontrivial finite quotient, since finite groups are MF. In particular `K` is not
  residually finite.
- `K` is not LEF. A LEF group is operator MF by `lef-implies-operator-mf`, so a LEF `K` would
  have `Rad_MF(K) = 1`, not `K`.
- `K` is not MF, for the same reason.

**Independent failure points.**
- (P1) alone is open and is not recorded anywhere in the graph. It asks for a finitely generated
  sofic Kazhdan group with no nontrivial MF quotient. The known Kazhdan full-radical groups have
  the wrong profile:
  - `defect-saturation-full-mf-radical`: soficity unknown;
  - `eighteen-relator-kazhdan-group-with-full-mf-radical`: not sofic;
  - Titz--Witzel residuals: both soficity and non-MF unknown.

  Known sofic Kazhdan groups without finite quotients, such as
  `simple-kazhdan-lef-group-from-minimal-subshift`, are LEF and hence MF. A **refutation** of (P1),
  that every sofic Kazhdan group has a nontrivial MF quotient, would kill this branch and the whole
  finite-outer-order region at once. It would also answer Alekseev--Thom 6.1 negatively in the
  strong form "every finitely presented sofic Kazhdan group has a nontrivial MF quotient".
- (P2), given a (P1) group, is a finiteness question about one automorphism. Hull--Osin style
  limits `R / union N_k` are natural (P1) candidates. There (P2) asks the normal subgroups `N_k` to
  be the orbit of finitely many relators under one automorphism of the free group, rather than an
  arbitrary increasing union.

## Attempts

**Attempt 1 (swarm-0917 w14-titz-pull, operator-algebras): orbit-full-group certificates for (P1).
Profinite hosts are dead. The claim stays OPEN.**

- **The class.** `permanence-closure-radical-witnesses-have-lef-kernels` shows that a (P1) group needs a
  soficity certificate from outside the permanence closure. Orbit full groups are the first survivor
  it names. The certificate is to embed `K` in a full group `[R]` of a sofic relation `R`.
- **Killed: profinite hosts.** `kazhdan-subgroups-of-profinite-orbit-full-groups-are-rf` proves that
  every Kazhdan subgroup of `[R_H]` is residually finite, for `R_H` the orbit relation of any ergodic
  profinite action of any countable group `H`. The proof is self-contained, with no imports. A (P1)
  group has no nontrivial finite quotient, so every homomorphism from it to such a full group is
  trivial.
  - The invariant is the normalized same-atom indicator `sqrt(n_i) 1_(Y_i)` in `L^2(X x X)`.
  - Every member dies at the finite action of `K` on the clusters of the fibre measure of the
    Kazhdan projection of that indicator.
- **Already dead in the graph.**
  - Amenable acting groups: `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`.
  - Haagerup acting groups when `K` is IRS-rigid:
    `irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups`.
- **What survives.** Non-profinite, for example mixing, actions of sofic groups `H` that are neither
  amenable nor Haagerup. These include Bernoulli shifts of residually finite Kazhdan groups, which have
  sofic orbit relations. The proof breaks exactly at its almost-invariance step (AI), because a mixing
  action has no generating refining sequence of `H`-permuted finite partitions. A (P1) group inside the
  full group of a Bernoulli shift of an RF Kazhdan group is the concrete remaining target for this
  certificate.
1. **Lacunary hyperbolic kernels (Hull--Osin and sparse hyperbolic-stage limits).** Dead at (P2)
   for the intended infinitely presented design (swarm-0917 w16, host-geometry). See
   `lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic`, which is ESTABLISHED from a verbatim
   import of the OOS proof of Theorem 3.3 and of Kapovich--Kleiner Theorem 8.1
   (`oos-lacunary-hyperbolic-short-relator-stages`).
   - *Stage sandwich.* For a lacunary hyperbolic `K = F(S)/N`, the OOS stages satisfy
     `N_{≤ C_2 k ℓ_k} = M_{n(k)} = N_{≤ ℓ_k}` with `ℓ_k → ∞`. So `K` is either hyperbolic or has
     unbounded relation gaps.
   - *Consequence.* The gap lemma of `relation-gaps-forbid-fp-mapping-tori` then gives:
     `(P2)` implies `K` is finitely presented, and hence `K` is hyperbolic.
   - *What a solution would be.* Any (P1)+(P2) pair with `K` quasi-isometric to a lacunary
     hyperbolic group is a finitely presented, torsion-free, hyperbolic, sofic Kazhdan group with no
     finite quotient. That is simultaneously a non-residually-finite hyperbolic group and an answer
     to Alekseev--Thom 6.1.
   - *Invariant and scope.* The invariant is the relation-gap ratio, which is at least
     `d_{n(k)} / ℓ_k = C_2 k`, the metric form of `δ_i = o(r_i)`. This kills the Hull--Osin
     candidates named above whenever their stages are hyperbolic with constants little-o of the
     injectivity radii.
   - *What survives.* (P1) candidates with no R-tree asymptotic cone, for example Burnside-type
     limits with `δ_i / r_i` bounded below. The node stays OPEN.
