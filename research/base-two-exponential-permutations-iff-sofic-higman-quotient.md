---
rg: 2
id: base-two-exponential-permutations-iff-sofic-higman-quotient
kind: claim
title: Order-four permutations that locally double exist for all large odd moduli iff Higman's group has a nontrivial sofic quotient
distinct_from:
  bs1m-higman-sofic-quotients-iff-exponential-permutations: that imports the equivalence for every base m between such permutations and sofic quotients of the cover H_k(BS(1,m)) into which BS(1,m) injects; this removes the injectivity requirement for base two and passes from the cover to Higman's group itself.
  order-four-exponential-permutations-exist-for-base-two: that is the open existence statement; this is the established equivalence that turns it into a question about sofic quotients.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**ESTABLISHED** by `base-two-permutations-sofic-quotient-reduction-proof`
(no novelty claimed beyond the combination).

**Statement.** Let `H4 = < a,b,c,d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >`.
The following are equivalent.

1. For every `eps > 0` there is `C` such that for every odd `n > C` there is
   `f` in `Sym(Z/nZ)` with `f^4 = id` and `f(x+1) = 2 f(x)` for at least
   `(1 - eps) n` values of `x`.
2. `H4` has a nontrivial sofic quotient.

**What it changes.**
- **Helfgott--Juschenko.** Their Theorem 2 (`thm:jut`, l.276–288 of
  arXiv:1512.02135) derives item 1 from soficity of `H4`. Item 2 asks only for
  some nontrivial sofic quotient.
- **Kassabov--Kuperberg--Riley.** Their Theorem `th-functions-BS` needs a sofic
  quotient of the cover `H_4(BS(1,2))` into which `BS(1,2)` injects. For base
  two that injectivity is automatic
  (`nontrivial-higman-quotients-keep-all-four-bs-subgroups`).
- **Amenable quotients.** Helfgott and Juschenko write that it is not known
  whether `H4` has amenable quotients (l.261–262). A nontrivial amenable quotient
  would give item 1, since amenable groups are sofic.
- **Where item 2 cannot come from.**
  `nontrivial-higman-quotients-are-not-locally-elementary-amenable` excludes
  every nontrivial quotient that is LEF, locally embeddable into elementary
  amenable groups, or residually elementary amenable.
  `nontrivial-higman-quotients-have-tower-distorted-generators` excludes every
  nontrivial quotient in which some generator has fixed-height iterated-exponential
  distortion.
