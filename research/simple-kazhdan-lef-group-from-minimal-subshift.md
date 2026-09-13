---
rg: 2
id: simple-kazhdan-lef-group-from-minimal-subshift
kind: claim
title: EL_3 over a minimal subshift algebra modulo its centre is an infinite simple Kazhdan LEF group
distinct_from:
  infinite-simple-kazhdan-hyperlinear-group: that is Pestov's existential question; this is one explicit group, which answers it in the stronger sofic form.
  binary-leavitt-elementary-group-is-simple: that group lives over a purely infinite ring and is nonsofic; this one lives over a stably finite ring that embeds in ultraproducts of matrix algebras, and is LEF.
  simple-kazhdan-kac-moody-lattices-exist: those groups are finitely presented and therefore never LEF; this group is infinitely presented and LEF.
invalidates:
  - simple-kazhdan-full-mf-radical-proof
  - fp-simple-full-mf-radical-via-titz-witzel
  - titz-witzel-exact-kazhdan-mf-radical-over-z-proof
  - titz-witzel-mapping-tori-are-virtually-products-proof
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
  - research/artifacts/ex-review-groups-2026-09-12-part1.md
  - research/artifacts/ex-pestov91-second-review-2026-09-13.md
  - research/artifacts/pestov-9-1-writeup-2026-09-13-part1.md
  - research/artifacts/pestov-9-1-writeup-2026-09-13-part2.md
  - research/artifacts/pestov-9-1-writeup-2026-09-13-part3.md
---

Let `q` be a prime power, `X` an infinite minimal subshift (for example Fibonacci), and
`R = LC(X,F_q) ⋊ Z`. Put `G = EL_3(R)` and `S = G / Z(G)`. Then `S` is a finitely generated group
which is:

1. infinite and simple;
2. Kazhdan;
3. LEF, hence sofic, hence hyperlinear.

It answers Pestov's Open Question 9.1 (arXiv:0804.3968, p. 21) positively in both the hyperlinear
and the sofic form. It also answers Ozawa's remark in *About the QWEP conjecture*
(arXiv:math/0306067), the origin of 9.1: "It is unknown whether there exists a simple property (T)
group Γ which is hyperlinear". `S` is also the marked limit of the finite simple groups
`PSL_(3N_k)(F_q)` (`finite-simple-groups-converge-to-simple-kazhdan-group`). It is operator MF and,
by Ozawa--Thom, not weakly quasidiagonal.

**Status.**
- Proof: route `simple-kazhdan-lef-group-from-minimal-subshift-proof`, with the full derivation in
  the Part 1 artifact.
- Independent review PASS by `ex-verify-groups` (`research/artifacts/ex-review-groups-2026-09-12-part1.md`,
  commit 0efeac410). Its wording notes are applied.
- Second independent review PASS by `ex-pestov91-harden`
  (`research/artifacts/ex-pestov91-second-review-2026-09-13.md`). It was landed at badc66e2d7 before the first
  review was opened, and compared with it at 80873d2cc7: no disagreement. Its notes are applied as forward
  corrections on 2026-09-13:
  - N1 (central idempotent in 4.2(c)) and N2 (radius bound for `psi_k`) in the Part 1 artifact;
  - N3 (scalar markings for `q` not prime) and N5 (primitive-root step checked) in
    `finite-simple-groups-converge-to-simple-kazhdan-group`;
  - N4 (stale review text) in `simple-kazhdan-hyperlinear-from-subshift-elementary-group`;
  - N6 (simplicity over fields) in the credits below and in `minimal-subshift-algebra-is-simple-lef-ring`.
- Write-up: a self-contained exposition in three parts, `research/artifacts/pestov-9-1-writeup-2026-09-13-part1.md`
  to `-part3.md`. It stays in the repository; publishing outside needs the user's approval.
- Novelty: bounded checks by this lane, by `ex-novelty` and by `ex-pestov91-harden` (write-up Part 3 §10) found no
  earlier infinite simple Kazhdan group that is LEF, sofic or hyperlinear.

## Credits

- **Property (T):** Ershov--Jaikin-Zapirain, arXiv:0809.4095, Theorem 1.1.
- **Simplicity of the ring:** `R` is the Steinberg algebra over `F_q` of the effective minimal transformation
  groupoid `Z ⋉ X`. The criterion for complex coefficients is Brown--Clark--Farthing--Sims, arXiv:1204.3127,
  Theorem 4.1. For arbitrary fields it is Steinberg, arXiv:1408.6014, Corollary 3.6 (PDF p. 10), and
  Clark--Edie-Michell, arXiv:1403.4684, Corollary 4.6 (PDF p. 7). Our case is proved directly in the artifact,
  with no dependence on these citations.
- **Periodic models:** the return-word approximation of minimal subshifts behind Grigorchuk--Medynets'
  LEF theorem for topological full groups (arXiv:1105.0719, Theorem 2.6), here in ring form.
- **Nearest prior art:** Thom, arXiv:0810.2180, Theorem 1.4, a finitely generated LEF Kazhdan group
  that is not residually finite and is not simple. `S` strengthens this to a simple group.
- **Kills recorded as graph structure.** The four routes listed under `invalidates:` all rested on
  "every infinite simple Kazhdan group has full MF radical". `S` refutes that statement.
- **New here:** passing to `EL_3` over the crossed-product ring, root detection through tower
  subrings, and the resulting simple Kazhdan LEF group.
