---
rg: 2
id: ternary-anti-central-kernel-unitization-not-directly-finite
kind: claim
title: The unitized evaluation kernel on the ternary anti-central summand carries a one-sided inverse pair
distinct_from:
  leavitt-evaluation-kernel-unitization-not-directly-finite: that is the binary kernel unitization in F_2[R^x]; this is the kernel of the evaluation on the anti-central summand of F_3[L_(F_3)(1,2)^x], where by Klein-corner transfer it is equivalent to failure of direct finiteness of the whole summand.
  ternary-anti-invariant-swap-corner-is-full: that is the specific corner equation c e_- b = eps_-, whose solutions are visible; this asks for any pair over eps_- with defect in the kernel, which that corner equation implies and which is not known to imply it.
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

**OPEN.** Let `S_- = eps_- F_3[G]`, `G = L_(F_3)(1,2)^x`, `pi : S_- -> R` the evaluation and
`K_- = ker pi`. Exhibit `u, v` in `K_-` with

    (eps_- + v)(eps_- + u) = eps_-,     (eps_- + u)(eps_- + v) != eps_-.

By `ternary-anti-central-failures-transfer-into-kernel-corners` this is equivalent to `S_-` not
being directly finite. Each implies that `G` is not surjunctive
(`ternary-invisible-pair-refutes-surjunctivity`).

## Necessary conditions

* **Defect.** `d = eps_- - (eps_- + u)(eps_- + v)` is an idempotent of `K_-` with Kaplansky trace
  `0`. It is not a single Klein kernel idempotent, whose trace is `2`.
* **No nilpotent parts.** `eps_- + n` with `n` nilpotent is a unit.
* **Not a finite-subgroup projective.** The defect is an idempotent `d` of `F_3[G]` with
  `F_3[G] ~= F_3[G] (+) d F_3[G]`.
  * By `lifted-trace-detects-finite-subgroup-projectives` (stated for every prime `p`), the lifted
    trace `t_3` is additive with `t_3(d) = 0`.
  * Every nonzero finite direct sum of projectives induced from finite subgroups has
    `t_3 = dim/|H| != 0`. So the Klein idempotent `q`, sums of orthogonal kernel character
    idempotents of finite sign-constant groups at deeper levels, and `q - mu(q)` are all excluded
    as defects, although the mod-3 trace allows sums of three of them.
  * What survives has to mix finite subgroups, for example `d = e - f` with `f < e` induced from
    different finite subgroups with equal lifted trace.
* **No finite-dimensional detection.** `G` is finitely generated, simple and infinite. So every
  finite-dimensional representation of `F_3[G]` factors through the augmentation, where `eps_-`
  acts as `0`. `S_-` has no nonzero finite-dimensional representation.

## Attempts

* **Kernel corners.** Universal: every failure of `S_-` lands in the corner of the Klein
  idempotent. So there is no easier sub-case, and no strict pair in any corner is known.
* **Radical perturbation.** Dead by `ternary-anti-central-kernel-has-klein-idempotents`: `K_-` is
  not in the radical.
* **Traces mod 3.** They do not separate kernel idempotents from `eps_-`; only evaluation does.
  The 3-adic lifted trace separates every finite-subgroup projective from a defect (see
  Necessary conditions).
* **Proper corner self-embedding.** Dead as a shortcut. `mu` embeds `S_-` unitally into the proper
  corner `q S_- q`, but a proper corner self-embedding does not make a ring directly infinite: the
  telescoping tail `mu^m(error)` stays nonzero at every finite depth. This is the same failure
  recorded on `leavitt-recursive-kernel-idempotents` over `F_2`.
* **Visible route.** The lift of `(s0 + s1, 2(t0 + t1))` feeds this claim through
  `anti-central-corner-gives-invisible-kernel-pair`. The unit criterion there asks the kernel for
  a unit in `eps_- + K_-`.
