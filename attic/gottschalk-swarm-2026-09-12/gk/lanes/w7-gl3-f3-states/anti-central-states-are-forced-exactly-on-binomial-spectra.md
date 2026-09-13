---
rg: 2
id: anti-central-states-are-forced-exactly-on-binomial-spectra
kind: claim
title: A K_0 state of the ternary anti-central summand is one spectral weight on minimal polynomials; it is forced to the lifted trace exactly at binomial spectra, and transpose-inverse acts by inversion
requires: [three-prime-leavitt-units-classified-by-minimal-polynomial]
distinct_from:
  anti-central-k0-states-equal-lifted-trace-on-signed-thompson: that forces states on finite subgroups conjugate into the signed Thompson group; this forces them on every finite subgroup whose three-regular elements have binomial minimal polynomials, and shows no finite-subgroup datum forces the rest.
  anti-central-k0-states-can-be-chosen-transpose-invariant: that normalizes one semidihedral split; this computes the action of transpose-inverse on all finite-subgroup data and says exactly which weights invariance kills.
artifacts:
  - research/artifacts/gl3-f3-anti-central-spectral-states-2026-09-12.md
---

**OPEN** (candidate proof in Attempts; re-derivation requested from `w4-vf-linear-b`).

Notation of `anti-central-state-exists-iff-lifted-trace-relatively-positive`. Let `s` be a state on
`(K_0(S_-), [eps_-])`.

1. There is a unique function `W_s` on three-regular units, depending only on the minimal polynomial `p_g`, odd under
   `z`, with `W_s(1) = 1` and `W_s(g^(-1)) = conj W_s(g)`, such that
   `s([p]) = (1/|K|) sum_(c in K three-regular) W_s(c) Phi_p(c)` for every finite `K` containing `z`.
   For the lifted trace, `W = delta_1 - delta_z`.
2. `W_s(g) = 0` whenever `p_g` is binomial and `g != 1, z`. So `s = trl` on `H_fin(K)` for every finite `K` with
   binomial three-regular spectrum, for example the constant `SL_2(F_3)`.
3. Data internal to finite subgroups force nothing more. For finite `K` and any admissible `U` supported on
   non-binomial classes, `trl + eps U` is a state on `K_0(eps_- F_3[K])` for small `eps`, agreeing with `trl` on
   everything induced from binomial subgroups.
4. `alpha(g) ~ g^(-1)` and `delta(g) ~ g`. So `alpha_*` acts by `W -> W o inv`, `delta_*` trivially, and an
   `alpha_*`-invariant state has real `W_s`, vanishing at `g` whenever `p_(g^(-1)) = p_(z g)`.

In `GL_2(F_3)` every non-binomial class satisfies that test, which recovers
`gl2-f3-anti-central-states-are-forced-by-semidihedral-blocks`. Section 2 of the artifact.

## Attempts

- *Candidate proof (w7-gl3-f3-states, 2026-09-12).*
  - (1) Nondegenerate pairing of projective Brauer characters with odd class functions on three-regular classes,
    together with Frobenius reciprocity along inclusions and the conjugacy classification.
  - (2) Theorem 1.3 and Theorem 2.1(b) of the Hadamard artifact on `<g, z>`, then uniqueness of `W`.
  - (3) Strict positivity of `trl` on projective indecomposables, and `Res_J U = 0`.
  - (4) The involution preserves minimal polynomials, inversion reciprocates them, and `delta` is an injective unital
    endomorphism.
- *Where it stops:* whether global positivity or `K_0` relations through infinite-order elements force non-binomial
  weights. That is the extension problem for the whole lifted trace (Remark 2.3 of
  `lifted-trace-state-extension-2026-09-12.md`), not the existence of a state.
