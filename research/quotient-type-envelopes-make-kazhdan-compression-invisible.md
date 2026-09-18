---
rg: 2
id: quotient-type-envelopes-make-kazhdan-compression-invisible
kind: claim
title: A sofic representation that is flexibly an honest finite action on a finitely generated normalized envelope cannot see a Kazhdan compression, so it kills every compression defect at that compressor
distinct_from:
  locally-residually-finite-targets-kill-compression-defects: that kills defects in homomorphisms to locally residually finite targets and uses no property (T); this kills them in representations into the universal sofic group, which is not locally residually finite, under a hypothesis on the restriction to the envelope only, and property (T) of the compressed group is what makes the finite-quotient identity survive approximation.
  centralizing-hnn-sofic-via-regular-edge-centralizer: that is the no-go for exact quotient models with an exact stable letter over a non-closed edge; this is the approximate version for compressed Kazhdan edges, where non-closedness is automatic, and it allows o(1) errors both in the envelope model and in the centralizing element.
  ascending-hnn-base-profinite-closure-telescope: that computes the profinite closure of the base inside the ascending HNN group, whose kernel is not finitely generated; this computes it inside an arbitrary finitely generated envelope normalized by the compressor, and upgrades it to the ultraproduct.
  kun-thom-sofic-centralizer-normalization: that proves normalization for infranormal Kazhdan pairs inside a Kazhdan ambient group for every sofic representation; this needs no infranormality and no property (T) of the envelope or of the compressor group, but only covers representations whose restriction to the envelope is quotient-type.
  compression-defect-dies-in-finite-dimensions: that kills defects in finite-dimensional linear representations by a commutant-dimension count; this is the permutation, normalized-Hamming statement, where no dimension is available.
  centralizing-hnn-perturbed-edge-separation: that asks for small perturbations of quotient models separating closure points of a general edge; this shows that for a compressed Kazhdan edge no o(1) perturbation of a quotient model can separate the compression pinches.
artifacts:
  - research/quotient-type-envelopes-make-kazhdan-compression-invisible-proof.md
  - research/locally-residually-finite-targets-kill-compression-defects.md
  - research/centralizing-hnn-sofic-via-regular-edge-centralizer.md
---

**ESTABLISHED.** Proof: `quotient-type-envelopes-make-kazhdan-compression-invisible-proof`.

## Setting

- `G` is a countable group and `u in G`.
- `M <= G` is finitely generated and `u M u^-1 = M`. Call `M` the envelope.
- `L <= M` has property (T), and `u L u^-1 <= L`.
- `N = ⋃_{j >= 0} u^-j L u^j <= M` is the compressor chain (telescope).
- `S_U = prod_U Sym(Omega_n) / {d_H -> 0}` is a metric ultraproduct of finite symmetric
  groups with the normalized Hamming distance `d_H`.

A homomorphism `sigma : G -> S_U` is **quotient-type on `M`** if there are finite sets
`Omega'_n ⊇ Omega_n` with `|Omega'_n| / |Omega_n| -> 1` along `U`, and honest actions
`rho_n : M -> Sym(Omega'_n)`, such that for every `m in M`

```text
sigma(m) = [ rho_n(m) restricted to Omega_n, patched arbitrarily to a permutation ]_U .
```

Equivalently, `sigma|_M` is flexibly the ultralimit of honest finite actions. The
exact case is `Omega'_n = Omega_n`.

## Statement

**(Q1) Profinite invisibility.** In every finite quotient `q` of `M`, `q(u L u^-1) = q(L) = q(N)`.
Equivalently, `N ⊆ cl_M(u L u^-1)`, the profinite closure of `u L u^-1` in `M`. If
`u L u^-1 != L`, then `u L u^-1` is not separable in `M`.

**(Q2) Uniform commutation.** Let `(S, kappa)` be a Kazhdan pair for `L`. Let `rho` be an
honest action of `M` on a finite set `Omega`, and let `c in Sym(Omega)`. Put

```text
delta = max_{s in S} d_H(c rho(u s u^-1), rho(u s u^-1) c).
```

Then `d_H(c rho(x), rho(x) c) <= 4 delta / kappa^2` for every `x in N`.

**(Q3) Ultraproduct normalization.** If `sigma : G -> S_U` is quotient-type on `M`, then

```text
C_{S_U}(sigma(u L u^-1)) = C_{S_U}(sigma(L)) = C_{S_U}(sigma(N)).
```

Hence `sigma(u)` normalizes `C_{S_U}(sigma(L))`, and `sigma(u^-1)` does too.

**(Q4) Defect kill.** Under (Q3), `sigma([u c u^-1, l]) = 1` for all `c in C_G(L)` and
`l in L`. More generally, `sigma([c, x]) = 1` for all `c in C_G(u L u^-1)` and `x in N`.

**(Q5) Group level.** If some quotient-type `sigma` is injective on the finitely many
elements `[c, x]` in question, those elements are trivial. In particular, if `G` has a
sofic embedding that is quotient-type on `M`, then `C_G(u L u^-1) = C_G(L)`, so `u`
normalizes `C_G(L)` and every defect generator at `u` is trivial.

## The class this kills

This bears on (CKN) of the wave-10 calibration `sofic-normalization-fails-for-finite-index-kazhdan-pairs`,
which is not in this tree. In the normalized case, (CKN) says: in a sofic group, a
Kazhdan `L` compressed by `u`, whose chain lies in a Kazhdan envelope normalized by `u`,
has its centralizer normalized by `u`.

(Q3)–(Q5) kill every counterexample construction of the following kind: the ambient
group is sofic through representations that are flexibly honest finite actions on the
envelope. This covers:

1. every residually finite or LEF envelope modelled by finite quotients;
2. the Følner level models of mapping tori `M ⋊_u Z` of residually finite `M`, where the
   `M`-action on each level is honest. For the mapping torus alone this already follows
   from (LRF), since it is residually finite. What is new is that the kill persists in
   every larger group whose approximations restrict to such models;
3. amenable-extension approximations (Elek–Szabó type) built over such level models,
   whenever the resulting model restricts to `M` as an honest action on each level
   (checked in Section 4 of the proof for mapping tori);
4. every centralizing HNN `<G, c | [c, u L u^-1] = 1>` modelled by a quotient model of
   `M` perturbed by `o(1)`. This holds even though `u L u^-1` is automatically
   non-separable by (Q1), which is the situation the exact no-go in
   `centralizing-hnn-sofic-via-regular-edge-centralizer` leaves open for perturbations.

**Where these constructions die.** In each honest finite model, the image of the
compressed copy equals the image of the whole chain (Q1). Property (T) of `L` then turns
approximate commutation with the generators of `u L u^-1` into uniform approximate
commutation with all of `rho_n(N)` (Q2). The would-be separating commutator `[c, l]` is
therefore `o(1)`-close to the identity.

**Invariant.** The profinite closure `cl_M(u L u^-1) ⊇ N`, read through the Kazhdan
constant of `L`.

## What survives

A (CKN) counterexample, and more generally a sofic witness with a nontrivial defect at a
compressor whose chain has a finitely generated normalized envelope, needs representations
whose restriction to the envelope stays macroscopically far from every honest finite
action, even flexibly. In other words, it needs a failure of flexible permutation
stability of `M` along the given representation.

For the route `(EK1)` of `torsion-free-sofic-extrinsic-kazhdan-defect-kernel`
(`G = K ⋊ Z`, `M = K`), this is automatic: a kernel with `Rad_MF(K) = K` has no finite
quotients, so it has no nontrivial honest finite actions. The present claim therefore
does not touch `(EK1)`. It only locates `(CKN)`: residually finite Kazhdan envelopes can
refute `(CKN)` only through sofic approximations that are flexibly unstable on `M`.
Becker–Lubotzky (*Group stability and property (T)*, J. Funct. Anal. 2020) show that
infinite residually finite Kazhdan groups are not permutation stable in the strict
sense. Their flexible stability is, to our knowledge, open, so it is unknown whether
residually finite Kazhdan envelopes can host a (CKN) counterexample at all. Envelopes
without finite quotients remain entirely open.

(CKN) itself stays **OPEN**.
