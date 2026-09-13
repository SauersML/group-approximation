---
rg: 2
id: gl3-f3-alpha-invariant-states-keep-three-free-spectral-weights
kind: claim
title: On the constant GL_3(F_3) the finite-subgroup data force a K_0 state only on binomial classes and leave three real spectral weights free after transpose-inverse averaging, so the GL_2 forcing argument stops at n = 2
requires: [anti-central-states-are-forced-exactly-on-binomial-spectra]
distinct_from:
  gl2-f3-anti-central-states-are-forced-by-semidihedral-blocks: that forces transpose-invariant states to the lifted trace on the constant GL_2(F_3); this shows the same inputs leave three real parameters on GL_3(F_3) and a free direction on every GL_n with n >= 3.
  anti-central-lifted-trace-is-relatively-positive: that is the positivity problem on the finite subgroups of the signed Thompson group; this measures what the constant GL_3(F_3) adds, and shows finite data add no relation.
artifacts:
  - research/artifacts/gl3-f3-anti-central-spectral-states-2026-09-12.md
---

**OPEN** (candidate proof in Attempts; re-derivation requested from `w4-vf-linear-b`). Whether some state, or every
state, equals the lifted trace on `H_fin(GL_3(F_3))` also stays OPEN.

Notation of `anti-central-states-are-forced-exactly-on-binomial-spectra`. Embed `GL_3(F_3)` in `G` by constants.
There is one conjugacy class of unital `M_3(F_3) -> R`, and `alpha` restricts to transpose-inverse. So `z = -I_3` and
`eps_- F_3[GL_3(F_3)] ~= F_3[SL_3(F_3)]`.

1. Of the 9 anti-central three-regular directions, 3 are binomial: `I`, `diag(1,1,-1)`, `J (+) 1`. The other 6 are
   `k_+ = B (+) 1`, `k_- = B (+) (-1)` with `p_B = x^2 + x - 1`, and four Singer classes of order 13.
2. Every state restricts to `s([p]) = trl(p) + (1/11232) sum_(c non-binomial) W_s(c) Phi_p(c)`. This is parametrized
   by `(mu, w_A, w_B) in C^3`, with `W(k_+) = mu`, `W(k_-) = -conj mu`, and `W = w_A, w_B, conj w_A, conj w_B` on the
   Singer classes. `alpha_*` acts by complex conjugation, so invariant restrictions keep 3 real parameters.
3. On `<k_+, z> ~= C_8 x C_2` the five anti-central idempotents take the values `1/8 +- Re mu / 2`, `1/4`, and
   `1/4 -+ (sqrt 2 / 2) Im mu`. Every small `(mu, w_A, w_B)` gives a state on `K_0(eps_- F_3[GL_3(F_3)])` that agrees
   with `trl` on classes induced from subgroups conjugate into `H`.
4. (Firewall.) For `n >= 3`, the finite data of `GL_n(F_3)` admit states other than `trl`. The finite data are:
   `W` is a class function of the minimal polynomial, `trl` holds on binomial subgroups, and `alpha_*` and `delta_*`
   invariance. So the GL_2 proof extends to `GL_n` iff `n <= 2`.
5. Some state has `mu = w_A = w_B = 0` iff `trl` is well defined and relatively positive on
   `H_fin(H) + H_fin(GL_3(F_3))`. No projective of `GL_3(F_3)` lowers the lifted trace intrinsically, since
   `trl(P) = dim P / 5616 > 0`.

Section 3 of the artifact.

## Attempts

- *Candidate proof (w7-gl3-f3-states, 2026-09-12).*
  - Items 1–3: the class table of Section 3.3, Theorem 2.1(c), Corollary 2.2 and Lemma 2.4 of the artifact, and a
    direct Brauer-character computation on `C_8` and `C_13`.
  - Item 4: Proposition 2.3 with `U = mu` on `(x - 1)(x^2 +- x - 1)` and `U = -mu` on `(x + 1)(x^2 +- x - 1)`.
  - Item 5: uniqueness of `W` on a finite subgroup, plus the state-extension argument of
    `anti-central-state-exists-iff-lifted-trace-relatively-positive`.
- *Not found:* a relation `[x] = [y]` in `K_0(S_-)`, with `x` from `GL_3(F_3)` and `y in H_fin(H)`, such that
  `trl(x) != trl(y)`. Equivalently, nothing forces `mu`, `w_A` or `w_B`. The trace-lowering stable relation from a
  `GL_3` projective asked for by the directive was not found, and by item 4 it cannot come from finite data alone.
- *Heuristic:* rationally, the extra `K_0` relations over `F_3` come from Nil terms, which are 3-primary. So if a
  degree-0 Farrell–Jones isomorphism held for `G` (not known), no linear relation would constrain `W`. The decision
  would then be about the positive cone `K_0^+(S_-)` alone.
