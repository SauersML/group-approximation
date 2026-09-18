---
rg: 2
id: thompson-f-amenable-via-idempotent-magma-measure
kind: route
title: Build an idempotent finitely additive measure on the free magma; it is invariant under re-association, which gives amenability of F
target: thompson-f-is-amenable
requires:
  - free-magma-carries-an-idempotent-finitely-additive-measure
---

**Imports** (J. T. Moore, *Nonassociative Ramsey theory and the amenability of Thompson's group*, arXiv:1209.2063v1,
§§2–3, read 2026-09-17). The withdrawal comment names only Lemma 4.13, which belongs to the existence half. The
following are from the sound half, verbatim:

> Theorem 3.3. If ν ∈ Pr(T) is an idempotent measure, then ν is F-invariant.

> The partial action of F on T canonically corresponds to the action of F on its positive elements with respect to
> the generating set xk (k ∈ N). It is well known that F is amenable if and only if this partial action is amenable
> (details can be found in, e.g., [13]). By amenability of the partial action, we mean that there is a ν in Pr(T)
> such that ν({t ∈ T : x1 · t and x2 · t are defined}) = 1, ν(x1 · Z) = ν(x2 · Z) = ν(Z) whenever Z ⊆ T.

Here `x1·((a^b)^c) = a^(b^c)` and `x2·(s^((a^b)^c)) = s^(a^(b^c))`, and [13] is Moore, arXiv:0905.1118.

**Route.** Let `ν` be given by `free-magma-carries-an-idempotent-finitely-additive-measure`. By Theorem 3.3, `ν` is
`F`-invariant in the sense quoted above. The proof in v1 §3 was re-checked, including the harmless `{a^1}` versus
`{1^c}` typo recorded in the prerequisite. By the quoted equivalence, `F` is amenable. The equivalence is imported,
not re-proved.

**Independence.** The prerequisite can fail while `F` is amenable. No argument is known that turns an invariant mean
on `F` into an idempotent measure on `T`, and `βT` contains no idempotent at all, by the parity homomorphism in the
prerequisite's Attempts. Its existence proof died at Lemma 4.13.
