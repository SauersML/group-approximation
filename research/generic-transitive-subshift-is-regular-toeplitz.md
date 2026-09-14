---
rg: 2
id: generic-transitive-subshift-is-regular-toeplitz
kind: claim
title: Pavlov–Schmieding Theorem 1.3 — a generic subshift in the closure of the infinite transitive subshifts is a regular Toeplitz subshift, minimal, uniquely ergodic, zero entropy, strongly orbit equivalent to the universal odometer
---

**ESTABLISHED by citation** (`generic-transitive-subshift-is-regular-toeplitz-citation`).

Source: R. Pavlov and S. Schmieding, *On the structure of generic subshifts*, arXiv:2203.15159v1 (29 Mar 2022). Read on 2026-09-13 from the arXiv PDF, pp. 1–4. Published as Nonlinearity 36(9) (2023) 4904–4953, doi 10.1088/1361-6544/acea25 (Crossref, checked by sk-verify-16); the journal numbering of the theorems was not checked.

- **Space.** `S` is the union over finite alphabets `A ⊂ Z` of the spaces `S[A]` of subshifts, with the Hausdorff metric (two subshifts are close when their sets of n-letter words coincide for large n). `S′` is the set of non-isolated points. `T′` is the set of infinite transitive subshifts in `S′`, and `T̄′` is its closure.
- **Theorem 1.3 (verbatim, p. 4).** "A generic subshift X in the closure T̄′ of the infinite transitive subshifts has the following properties:
  (1) X is a regular Toeplitz subshift (and hence is minimal, uniquely ergodic, and has zero entropy) which factors onto the universal odometer (Theorem 5.15).
  (2) X has topological rank two (Corollary 5.29).
  (3) X is strong orbit equivalent to the universal odometer, and in particular, the dimension group of X has rank one and hence no nontrivial infinitesimals (Corollary 5.32)."
- **Clopen restriction (p. 3).** "For any nonempty shift of finite type X, the subshifts contained in X form a clopen subset of S (see Lemma 2.3)". So for a fixed finite alphabet `A`, `T̄′ ∩ S[A]` is open in `T̄′`, and a generic property in `T̄′` is generic in `T̄′ ∩ S[A]`.

**Review (sk-verify-15, 2026-09-13): PASS.** Theorem 1.3 (source label maintrans, e-print l.234–240), the clopen restriction (l.197) and perfectness of the infinite transitive subshifts (l.154) checked verbatim in arXiv:2203.15159v1. See `research/artifacts/sk-verify-15-2026-09-13-part3.md` §5.

**Review (sk-verify-16, 2026-09-13): PASS-WITH-FIXES.** Theorem 1.3(1)–(3), the perfectness sentence and the Lemma 2.3 sentence checked verbatim against the arXiv:2203.15159v1 PDF (extracted on MSI). Journal data from Crossref applied. See `research/artifacts/sk-verify-16-2026-09-13.md` §8.
