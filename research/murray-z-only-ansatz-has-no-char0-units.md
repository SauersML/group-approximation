---
rg: 2
id: murray-z-only-ansatz-has-no-char0-units
kind: claim
title: Murray's z-only unit ansatz on the Promislow group has only the trivial solution in characteristic zero
distinct_from:
  gardam-support-pair-has-no-rational-units: that fixes Gardam's 21-element support pair and allows any coefficients on it; this fixes the ansatz shape and the inverse formula but lets the f_i be arbitrarily long, so the supports are unbounded.
  unit-conjecture-fails-over-complex-numbers: that imports nontrivial units of C[P] on Gardam's support pair; this shows that no unit of Murray's shape with Gardam's inverse formula exists over any field of characteristic zero, C included.
  support-pair-unit-scheme-is-finite-over-z: that bounds the units on one fixed support pair; this excludes one ansatz family at every support size.
  promislow-radius4-one-sided-and-integral-separation: that is a radius-four census over F_2 with an integral lifting obstruction; this is a structure theorem for an infinite family with no radius bound.
  rational-unit-conjecture-torsion-free: that is the open conjecture for every torsion-free group; this excludes one ansatz on one group.
---

**ESTABLISHED.** Let `P = <a, b | b^-1 a^2 b = a^-2, a^-1 b^2 a = b^-2>` and
put `x = a^2`, `y = b^2`, `z = (ab)^2`. They generate a free abelian subgroup
of index 4 with coset representatives `1, a, b, ab`. Let `K` be a field of
characteristic 0 and write `f^*(z) = f(z^-1)` on `K[z^{+-1}]`.

*Murray's ansatz* (arXiv:2106.02147, Section 4). For `f_1, ..., f_7` in
`K[z^{+-1}]` put

    p = (1+x)(1+y) f_1
    q = (1+x)(x^-1+y^-1) f_2 + (1+y^-1) f_3
    r = (1+y^-1)(x+y) f_4 + (1+x) f_5
    s = (x+4+x^-1+y+y^-1) f_6 + f_7

and `u = p + q a + r b + s ab`. *Gardam's inverse formula* is
`u' = x^-1 p_yz - x^-1 q a - y^-1 r b + z^-1 s_yz ab`, where `_yz` inverts
`y` and `z` (equivalently, conjugation by `a`).

**Theorem.** If `u'u = 1` in `K[P]`, then `f_1 = ... = f_6 = 0` and
`u = +-z^k ab` for some `k in Z`.

So no nontrivial unit of `C[P]`, `Q[P]` or `Z[P]` has Murray's shape with
Gardam's inverse formula. Murray's Theorem 2 (over `F_3`) and Theorem 3 (over
`F_d` for every odd prime `d`) solve the same equations, so the obstruction is
specific to characteristic 0.

*Structure.* When `f_2 != 0`, the equations force `rho = f_4 / f_2` to satisfy
`rho rho^* = 1`, and

    f_1 = c f_6,   f_3 = z^-1 rho c f_2,   f_5 = c f_2,   c = rho + z rho^-1.

The system then reduces to `g N_6 = f_7^* f_6 + f_6^* f_7`, where
`N_6 = f_6^* f_6`, `g = w + w^-1 - 2` and `w = z^-1 rho^2`. Write
`rho = +-z^s B^* / B` in lowest terms, with `B` a polynomial of degree `n`,
and put `Delta = B^2 - z^(2s-1) B^*2`. Then every zero of `Delta` must be a
double zero of `psi2 + u psi2^*`, where `psi2` is a Laurent polynomial of span
at most `n` coprime to its reciprocal and `u` is a monomial. `Delta` has span
at least `2n + 1`, so a Wronskian bound excludes this. In characteristic `d`
the Wronskian can vanish while its quotient is not constant, and Theorem 3 is
exactly that case, with `B = 1`.

*Checks.* In mode `verify`, `research/artifacts/murray-z-only-ansatz-check.py`
computes `u'u - 1` in the affine model of `P`, with the `f_i` and `f_i^*` as
independent symbols. It finds that the coefficients of `u'u - 1` with their
`*`-images and Murray's six equations with theirs span the same `Q(z)`-space,
of rank 12. So over a field of characteristic 0 the six equations are
equivalent to `u'u = 1`. The same run confirms Theorem 3 over `F_3`, `F_5` and
`F_7` for `t in {-1, 0, 1, 2}` and both shifts, and shows that it fails over
`Q`. Results: `research/artifacts/murray-z-only-ansatz-char0-2026-09-12.md`.

*Scope.* The ansatz fixes two things: every `f_i` depends on `z` alone, and the
inverse is given by Gardam's formula. Units of `K[P]` of any other shape are
not covered.

DERIVATION
[[murray-z-only-ansatz-has-no-char0-units-proof]]
