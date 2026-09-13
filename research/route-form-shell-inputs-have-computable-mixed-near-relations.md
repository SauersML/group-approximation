---
rg: 2
id: route-form-shell-inputs-have-computable-mixed-near-relations
kind: claim
title: Inputs with an infinite cyclic direct factor admit computable enumerations whose near shift group satisfies a mixed relation
distinct_from:
  arithmetic-near-shift-actions-have-mixed-relations: that derives a mixed relation from a regular permutation with eventual residue-affine formulas; this constructs, for every input with an infinite cyclic direct factor, an enumeration in which one generator acts by an explicit residue-affine permutation while every other generator stays unconstrained.
  decidable-inputs-have-computable-non-fp-shell-envelopes: that constructs computable enumerations whose near shift group is the free product P*<s>, so their envelopes are not finitely presented; this constructs computable enumerations whose near shift group is not that free product, so the free-near-shift obstruction does not apply to them.
  decidable-inputs-have-fp-shell-envelopes: that asks for a finitely presented envelope; this only removes one necessary obstruction and asserts no finite presentation.
artifacts:
  - research/artifacts/shell-envelope-local-tests-2026-09-13.md
---

Let `P = P_0 x <t>` with `P_0` countably infinite and `t` of infinite
order. Let `lambda'` be the permutation of `N = {0,1,2,...}` given by

    lambda'(4k)   = 8k,       lambda'(4k+1) = 2k+1,
    lambda'(4k+2) = 8k+4,     lambda'(4k+3) = 4k+2,

except that `lambda'(0) = 1`, `lambda'(1) = 2` and `lambda'(3) = 0`.

Then:

1. There is a bijection `nu: P -> N` whose left regular permutations
   `lambda_g(nu(h)) = nu(gh)` satisfy `lambda_t = lambda'`.
2. For such `nu`, `[lambda_t s^4 lambda_t^-1, s^8] = 1` in `NearSym(N)`,
   where `s: n -> n+1`. This is a nonidentity reduced word of `P*<s>`,
   so the near shift group `R_nu = <lambda(P), s>` is not `P*<s>`, and
   `free-shift-shell-envelopes-are-not-finitely-presented` does not
   apply to `E_nu`.
3. If `P_0` has decidable word problem, `nu` and its inverse can be
   computed.

The regular permutations of `P_0` are `lambda_x(nu(y,k)) = nu(xy,k)`.
The construction places no restriction on them, so it imposes no
complexity bound on the germs of `lambda(P_0)`. No finite presentation
of `E_nu`, its singularity stabilizers or its germ group is asserted.

The shell route `boone-higman-via-fp-shell-envelopes` already replaces
its input by `P_0 x Z`. So its inputs always have this form, provided
`P_0` is infinite.
