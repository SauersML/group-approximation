---
rg: 2
id: thompson-v-haar-regular-gluings-have-defect-two
kind: claim
title: Haar-random unitary gluings of regular S4 and S3 representations converge in distribution to the regular representation of S4 *_Z2 S3, so every Thompson V relator has operator-norm defect tending to 2 and normalized Hilbert--Schmidt defect tending to sqrt 2
distinct_from:
  thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words: that proves V hyperlinear iff some W in the commutant U(12k) x U(12k) makes the four words nearly fixed; this computes the Haar-typical behaviour on that same parameter space. The four words are asymptotically maximally unfixed, and the good set has Haar measure tending to 0.
  thompson-v-gap-witnesses-need-unbounded-lie-closure: that proves gaps on the imprimitive, virtually abelian and bounded-Lie-closure strata of G0-representations; this treats the complementary generic stratum (Haar gluings, a.s. Zariski dense images of unbounded dimension) and proves defect 2 there, rather than a gap.
  thompson-gap-witnesses-need-nonamenable-image: that proves D >= 1/2 on virtually solvable images; this is about the generic nonamenable image and gives the asymptotically maximal value 2.
  thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes: that reduces V not MF to a uniform gap over nontrivial irreducibles of G0; this shows that the Haar-probabilistic method cannot produce the low-defect witnesses in the regular gluing fibre, in either norm.
  thompson-v-has-full-mf-radical: that is the open target; this is a class-kill for random constructions of MF witnesses and is not an answer.
artifacts:
  - experiments/thompson-v-random-gluing-defect-2026-09-17/random_gluing.py
  - experiments/thompson-v-random-gluing-defect-2026-09-17/out_random_gluing.txt
---

**ESTABLISHED** by `thompson-v-haar-regular-gluings-have-defect-two-proof` (a written proof, not yet reviewed). It
uses the Collins asymptotic-freeness theorem, imported in
`collins-haar-constant-matrices-asymptotic-freeness`, and a finite computation of the syllable structure of
`r5, ..., r8` (Part 1 of the artifact).

## Statement

Notation is as in `thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`:

```text
G0 = S4 *_<a> S3 = < a, b, c | a^2, b^3, (ab)^4, c^2, (ac)^3 >,     V = G0 / << r5, r6, r7, r8 >>.
```

- `tr` is the normalized trace on `M_n(C)`.
- `||x||_2 = tr(x^* x)^(1/2)`, and `||.||` is the operator norm.
- For `k >= 1` put `n = 24k` and `m = 12k`.

**The model.**
1. Fix representations `rho4 = lambda_S4 (x) 1_k` of `S4` and `rho3 = lambda_S3 (x) 1_(4k)` of `S3` on `C^n`.
2. Write both in bases where `rho4(a) = rho3(a) = A := diag(1_m, -1_m)`. Such bases exist because, in both regular
   representations, `a` has eigenvalues `+1` and `-1` with equal multiplicity.
3. For `U = U1 (+) U2` in `U(m) x U(m)`, which is the commutant of `A`, let `sigma_U` be the representation of `G0`
   given by `sigma_U|S4 = rho4` and `sigma_U|S3 = U rho3 U^*`.
4. By the standard form in `thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words`, these are, up to
   conjugacy, exactly the unitary free gluings of size `n`.
5. Let `U1` and `U2` be independent Haar unitaries in `U(m)`.

**Theorem.**
- **(i) Distribution.** For every `g` in `G0`, `tr sigma_U(g) -> delta_(g,e)` in probability as `k -> infinity`. So
  `sigma_U` converges in distribution to the left regular representation of `G0`.
- **(ii) Relators.** For `i = 5, ..., 8`, the eigenvalue distribution of `sigma_U(r_i)` converges weakly in probability
  to Haar measure on the circle. Consequently:
  - `||sigma_U(r_i) - 1|| -> 2` in probability;
  - `||sigma_U(r_i) - 1||_2 -> sqrt 2` in probability.
- **(iii) Every cyclically alternating word.** More generally, (ii) holds with `r_i` replaced by any `w` in `G0` of
  infinite order.
- **(iv) Rate.** For each fixed `g`, `P(|tr sigma_U(g) - delta_(g,e)| >= epsilon) = O(k^(-2))`. Hence, for a
  sequence of independent choices, the convergence in (i) and (ii) holds almost surely.

**Consequences for the search for witnesses.**
- For every `epsilon > 0`, the Haar measure of the gluing parameters `W` in `U(12k) x U(12k)` with
  `max_i ||r_i(sigma_W) - 1||_2 <= sqrt 2 - epsilon` tends to 0. The same holds for the operator norm with `2 - epsilon`.
- The good sets of criterion 4 in `thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words` (HS error at most
  `epsilon`) therefore have vanishing Haar measure. The same is true of the gluing fibre of the operator-norm MF
  criterion.
- So Haar sampling, and any argument that finds a witness with positive probability under a measure uniformly
  comparable to Haar, cannot prove that V is hyperlinear or MF. This does not rule out small good sets.

## Where the method dies

This is a class-kill for probabilistic constructions in the regular gluing fibre.
- **Invariant.** Freeness over the diagonal algebra of `A`, supplied by the Haar gluing. Together with the vanishing of
  the diagonal blocks of `lambda(x)`, `x` not in `<a>`, it forces `tr sigma(w) -> 0` for every cyclically alternating
  `w`.
- **Step where every member dies.** Each relator of V is, up to conjugacy, cyclically alternating in `G0`. The cyclic
  syllable lengths are 10, 20, 16 and 28 for `r5, r6, r7, r8` (Part 1 of the artifact, exact). So in the limit every
  relator sees `lambda_G0`, where it has Haar spectrum, and not V.
- **Scope of the proof.** Written for the exactly regular fibre `lambda (x) 1`. The proof uses only two properties:
  - the constant matrices have a joint limit distribution;
  - diagonal blocks of non-`<a>` elements have vanishing limit trace.
  So it applies verbatim to any sequence of balanced pairs `(rho4, rho3)` with `rho4(a) = rho3(a) = A`, characters
  `o(n)` off the identity, and a joint limit distribution of the blocks.
