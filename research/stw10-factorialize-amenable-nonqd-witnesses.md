---
rg: 2
id: stw10-factorialize-amenable-nonqd-witnesses
kind: claim
title: Amenable non-QD traces admit factorial witnesses
distinct_from:
  ideal-central-components-retain-an-amenable-nonqd-witness: that splits a fixed trace along one chosen ideal support but does not produce an extreme or factorial trace; this uses the whole amenable-trace face to obtain a factorial witness.
  exact-gns-kernel-amenability-reduction: that descends one trace to a faithful GNS quotient under exactness; this first factorializes the trace and consequently identifies the infinite-dimensional GNS closure with the hyperfinite II1 factor.
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks whether the trace on R itself is QD; this reduction concerns traces on arbitrary weakly dense C-star subalgebras with GNS closure R and does not assert QD descent between either algebra and R.
artifacts:
  - research/artifacts/stw10-factorial-witness-audit-2026-08-30.md
---

**ESTABLISHED FACTORIAL-WITNESS REDUCTION.**  Let `A` be a unital C-star
algebra carrying an amenable tracial state which is not quasidiagonal.  Then
there are a separable unital C-star subalgebra `B subset A` and an amenable
non-quasidiagonal tracial state `sigma` on `B` such that `sigma` is extreme
in `T(B)`.  Equivalently, the GNS von Neumann algebra

```text
pi_sigma(B)''
```

is a factor.

More precisely, on every separable unital `B`, all amenable traces are QD if
and only if all extreme amenable traces are QD.  Thus STW Problem X(1) is
equivalent to its restriction to separable factorial amenable traces.

If the original algebra `A` is exact, the witness can be sharpened further:
there is a separable exact unital C-star algebra `C` with a faithful amenable
non-QD trace `bar_sigma` such that

```text
pi_(bar_sigma)(C)'' is isomorphic to R.                       (FW1)
```

Consequently, a counterexample inside the class of exact C-star algebras
exists if and only if one exists with all the properties in `(FW1)`.  As a
positive corollary, if every extreme amenable trace on a separable unital
algebra has finite-dimensional GNS representation, then every amenable trace
on it is quasidiagonal.

DERIVATION
stw10-krein-milman-factorial-witness-proof
