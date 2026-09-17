---
rg: 2
id: fpbs-high-girth-uniform-l2-patch
kind: claim
title: Marked groups of girth at least L(eta) and spectral radius at most 1-eta have an l2 gap with explicit uniform constants
distinct_from:
  fpbs-free-product-cayley-graphs-have-critical-l2-gap: that proves a critical l2 bound on free products on union generating sets by a block-tree Schur test; this proves a gap with constants depending only on eta and the number of generators on every high-girth marked group, with no product structure.
  fpbs-spectral-margin-survives-product-generator-moves: that proves p_c < p_u when 1 + h - ||A|| > 0 and tracks it through generator moves; this needs no expansion margin, only girth and a spectral gap, and gives uniform l2 constants.
  fpbs-l2-gap-class-closed-under-local-limits: that shows each uniform class U_(M,delta) is closed; this exhibits an explicit clopen set of marked groups inside one fixed U_(M,delta).
  fpbs-l2-gap-baire-dichotomy: that is the Baire dichotomy and kernel on X_(k,eta); this is one explicit uniform patch, which removes the high-girth groups from the kernel at the first stage.
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
  - research/artifacts/fpbs-high-girth-uniform-l2-patch-proof-attempt-2026-09-17.md
---

**OPEN.** A drafted proof (Proposition 3.0, Theorem 3.1 and Corollary 3.2 of
`research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`) is recorded as an
attempt (see Attempts). It is not established because it was landed in the
same result as `fpbs-l2-gap-baire-dichotomy`, which it requires and which two
referee lenses refuted as written.

Let `C` be the absolute constant of Benjamini–Nachmias–Peres
(arXiv:0901.4616, Theorem 1). For `eta in (0,1)` and `k >= 2` put

```text
L(eta)       = max(3, ceil(4 C log(1 + eta^-2) / eta))
M(eta)       = 1 + 3/eta^2
delta(k,eta) = eta / (4(2k-1))
```

Let `(Gamma; s_1,...,s_k)` be a marked group with no nontrivial freely reduced
word of length less than `L(eta)` trivial in `Gamma`, and suppose the simple
Cayley graph `G` on `S = {s_i^{+-1}}` has spectral radius `rho <= 1 - eta`.
Then `G` is `2k`-regular with girth at least `L(eta)`, and

```text
||T^G_{p_c(G) + delta(k,eta)}||_{2->2} <= M(eta),
```

so `p_c(G) + eta/(4(2k-1)) <= p_{2->2}(G) <= p_u(G)`.

The set of such marked groups is relatively clopen in the compact space
`X_{k,eta}` of `fpbs-l2-gap-baire-dichotomy`. Hence the kernel `K_{k,eta}`
lies in the finite union of relator cylinders
`Z_{k,eta,w} = {w = e}`, over nontrivial reduced `w` with `|w| < L(eta)`.

Without the girth hypothesis, the same path count gives, for every
vertex-transitive `d`-regular graph with `d >= 3` and `rho < 1`, the bound
`||T_q|| <= 1 + (d/(d-1)) r/((1-r)(1-rho))` whenever
`r = q(d-1)rho < 1`. So `p_{2->2} >= 1/((d-1)rho)`.

Nachmias–Peres (arXiv:1207.1480, Theorem 1) state only `p_c < p_u` under these
hypotheses. The new content is the explicit uniform l2 constants, which is the
form the closed-class transplant and the Baire kernel consume.

## Attempts

1. **Nachmias–Peres path counting with the Benjamini–Nachmias–Peres girth bound
   (2026-09-17).** Formerly the route `fpbs-high-girth-uniform-l2-patch-proof`
   (requires [fpbs-l2-gap-baire-dichotomy]); see
   `research/artifacts/fpbs-high-girth-uniform-l2-patch-proof-attempt-2026-09-17.md`
   and Section 3 of `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.
   Demoted on 2026-09-17 after the referee pass on the result that also
   produced `fpbs-l2-gap-baire-dichotomy`. Lenses 1 and 3 refuted that result
   over the dichotomy claim's sentence that a gap failure "is never isolated in
   the marked-group topology", which does not follow from Theorem 2.2 (an
   isolated point of `X_(k,eta)` outside `C_2`, such as a marking of a finitely
   presented simple nonamenable group, would be a singleton kernel). No lens
   objected to this claim: lenses 2 and 3 checked Proposition 3.0, Theorem 3.1
   and Corollary 3.2 line by line (`r = (1+rho)/2`, `||T_q|| <= 1 + 3/eta^2`,
   the margin `q - 1/(d-1) >= eta/(2(d-1))`, the BNP step with
   `lambda_1 = 1 - rho >= eta`, the girth bound, `q < 1/2`) and found no
   unfilled step. Restore the route once the dichotomy claim is repaired and a
   full referee pass survives.
