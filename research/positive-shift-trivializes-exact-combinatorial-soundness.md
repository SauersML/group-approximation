---
rg: 2
id: positive-shift-trivializes-exact-combinatorial-soundness
kind: claim
title: Adding a small multiple of the identity to every term makes exact combinatorial soundness and rounder cost vacuous
artifacts:
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
distinct_from:
  combinatorial-gap-and-rounder-give-energy-gap: that is the two-sided identity for one fixed Hamiltonian; this is an instance transformation applied uniformly to every instance of a reduction, forcing combinatorial gap one and a bounded rounder constant while scaling the promise gap by a constant factor.
  qubit-pairs-have-half-gap-and-unbounded-rounder-cost: that exhibits positive combinatorial gap with unbounded rounder cost at vanishing energy; this shows positive combinatorial gap and bounded rounder cost can be manufactured on every instance, YES included, so neither carries promise information by itself.
---

**ESTABLISHED (ordinary proof; not a Lean certificate).** Let
`H=(1/m) sum_a h_a` on a nonzero finite-dimensional space with `0<=h_a<=I`,
and fix a rational `epsilon` in `(0,1)`. Put

```text
h'_a = (1-epsilon) h_a + epsilon I,    H' = (1-epsilon) H + epsilon I.    (PS0)
```

1. **(PS1)** `h'_a` acts on the support of `h_a`, and `0<=h'_a<=I`. The term
   count and local dimension are unchanged. Rational entries grow by
   `O(log(1/epsilon))` bits.
2. **(PS2)** `Tr(h'_a sigma)>=epsilon` for every normalized `sigma`, so no
   state satisfies any shifted term exactly. Thus `s*(H')=m`, and `H'` has
   combinatorial gap one.
3. **(PS3)** `lambda_min(H')=(1-epsilon)lambda_min(H)+epsilon>=epsilon`, and
   the least rounder constant of `H'` is `1/lambda_min(H')<=1/epsilon`.
4. **(PS4)** If YES instances satisfy `lambda_min(H)<=a` and NO instances
   satisfy `lambda_min(H)>=b`, the shifted thresholds are `(1-epsilon)a+epsilon`
   and `(1-epsilon)b+epsilon`, a promise gap of `(1-epsilon)(b-a)`.
5. **(PS5)** Use the trivial syndrome data: `W psi=|1...1> tensor psi`, `B_a`
   the projector onto flag `a` reading one, `N(a)={a}`, `C_0=1/epsilon`,
   `R=1`. These projectors commute, are local, and satisfy
   `W^* B_a W=I<=(1/epsilon)h'_a`. Every infeasible fault label has zero
   effect, the only outcome is `S=[m]`, and the conditioned exactifier is
   vacuous.
6. **(PS6)** Say `H` has `(beta,eta)`-robust combinatorial gap if every
   normalized `sigma` and `S` with `Tr(h_a sigma)<=eta` for all `a` outside
   `S` satisfy `|S|>=beta m`. A `(beta,eta)`-robust gap gives
   `lambda_min(H)>=beta eta`. Conversely, `lambda_min(H)>=b` gives a
   `(b-eta,eta)`-robust gap for `0<eta<b`.

**Reading.** Exact combinatorial soundness (`eta=0`), a bare rounder constant,
and trivial local syndrome ports carry no promise information for reductions
with imperfect completeness. After the shift, every instance, YES and NO, has
combinatorial gap one and rounder constant at most `1/epsilon`. These notions
become informative only jointly with a constant YES margin, or on families
whose YES outputs are frustration-free, which the shift destroys. With a
positive tolerance `eta`, robust combinatorial soundness is energy soundness
up to constants. The application to the anchored-amplifier region is
`anchored-criterion-components-are-shift-satisfiable`.
