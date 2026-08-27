---
rg: 2
id: thin-selected-module-is-profinite-continuous
kind: claim
title: A selected thin-central leak from matrices is continuous for the finite-dimensional lattice norm
distinct_from:
  sl3-z-weakly-ucp-stable: that corrects the whole approximate lattice representation; this asks only for weak containment of one cyclic conjugation module in the direct sum of finite-dimensional nontrivial sectors.
  tempered-selected-conjugation-vector-obeys-rcc: that asks for reduced-norm continuity; this weaker profinite continuity allows every congruence representation of SL_3(Z).
  canonical-trace-does-not-weaken-thin-commutant-transfer: that shows actor-character information is camouflaged by residual-finite tensor factors; this asks for mixed selected-vector coefficient continuity, which actor traces do not determine.
---

Fix the explicit pair

```text
A=SL_3(Z),  C=<a,b>
```

from `explicit-sl3-thin-codense-tau-pair`.  Let `U_k` be an asymptotic
matrix representation of a fixed presentation of `A`, let `pi:A->U(M_omega)`
be the induced ultraproduct representation, and let `v in U(M_omega)` commute
with `pi(C)`.  With `P_A`, `eta`, and `K_v` as in `(PSG2)`, assert

```text
Ad pi|_(K_v) is weakly contained in pi_FD^0,            (SPC1)
```

where `pi_FD^0` is the direct sum of the non-`A`-invariant parts of all
finite-dimensional representations of `A`.

Equivalently, the selected positive-definite coefficient state generated
by `(1-P_A)v` is continuous for the C-star seminorm obtained from all
finite-dimensional representations of `SL_3(Z)`.  No correction of `U_k`,
and no continuity assertion for the rest of `L^2(M_omega)`, is requested.

This is the smallest currently isolated spectral modulus that closes the
thin HNN route.  The exact finite-dimensional theorem already puts a
uniform `C`-gap on `pi_FD^0`; `(SPC1)` is precisely the missing passage from
matrix presentation coordinates to that one selected quotient.

## Firewalls

1. Canonical actor trace does not imply `(SPC1)`: residual-finite tensor
   camouflage preserves actor moments while leaving the auxiliary selected
   module untouched.
2. Scalar positive-definiteness does not imply `(SPC1)`: the exact
   quasiregular representation on `l^2(A/C)` contains a `C`-fixed vector and
   is therefore discontinuous for this seminorm.
3. Matrix origin is essential.  In a canonical regular embedding of the
   thin centralizer HNN group, the stable-letter orbit is exactly the
   quasiregular frame on `A/C`; thus a hypothetical hyperlinear embedding is
   an explicit counterexample to `(SPC1)`.  This obstruction is formalized
   by `thin-hnn-regular-selected-module-is-profinite-discontinuous`.
4. Existing stability in finite actions and weak-ucp stability would give
   much stronger correction statements, but neither is known here.  The
   present claim does not follow from property `(T)`, property `(tau)`, or
   profinite co-density alone.

## Attempts

- **Correct the whole actor tuple.**  Weak-ucp or flexible HS stability would
  replace the asymptotic `A`-representation by finite-dimensional exact
  representations and prove `(SPC1)`.  This is substantially stronger, and
  no such theorem is known for `SL_3(Z)`.
- **Use only the actor character.**  This dies by residual-finite tensor
  camouflage: one can impose the canonical actor trace without changing the
  selected auxiliary module.
- **Apply property `(tau)` directly to the selected vector.**  The gap acts
  only after continuity for the finite-dimensional norm is known.  The exact
  quasiregular `A/C` module supplies a `C`-fixed mean-zero vector and shows
  that no representation-independent Laplacian inequality can establish
  that continuity.
- **Round an associated permutation action.**  This reduces to stability in
  finite actions for a proper Kazhdan permutation-co-dense subgroup; the
  required nonnormal relative form is not supplied by the current
  Alekseev--Thom theorem.  In the other direction,
  `sofic-thin-coset-action-refutes-selected-profinite-continuity` proves that
  any sofic atlas for `A curvearrowright A/C` outright refutes `(SPC1)`.

**Status: OPEN.**

For the terminal transfer theorem this claim is stronger than necessary.
`thin-leak-has-universal-fd-null-laplacian-witness` constructs one explicit
sequence `(y_N)` with exponentially vanishing finite-dimensional norm which
detects every leak.  The smaller open claim
`thin-selected-fd-null-cutoff-cannot-survive-matrices` asks for continuity
only on that sequence and that selected vector.
