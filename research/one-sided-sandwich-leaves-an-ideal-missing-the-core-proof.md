---
rg: 2
id: one-sided-sandwich-leaves-an-ideal-missing-the-core-proof
kind: route
title: The unilateral shift realizes pq=1 with qp!=1, and the Laurent quotient keeps the scalars
target: one-sided-sandwich-leaves-an-ideal-missing-the-core
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Work in `T = k<p, q | pq = 1>`.

**A representation separating `qp` from `1`.**  Let `V` have basis
`e_0, e_1, e_2, …` and define

    q(e_n) = e_{n+1} ,        p(e_0) = 0 ,   p(e_{n+1}) = e_n .

Then `pq(e_n) = p(e_{n+1}) = e_n`, so `pq = 1`, and the relation of `T` is
satisfied.  But `qp(e_0) = q(0) = 0 != e_0`, so `qp != 1`.  Hence

    e = 1 - qp

is a nonzero element of `T`.  (It is the idempotent projecting onto `e_0`.)

**The ideal is proper.**  Let `J = TeT`.  There is a unital homomorphism

    T ->> k[t, t^{-1}] ,      q |-> t ,   p |-> t^{-1} ,

well defined because `t^{-1} t = 1`.  It sends `qp |-> t t^{-1} = 1`, so
`e |-> 0`, so `J ⊆ ker`.  The Laurent polynomial ring is nonzero, hence
`J != T`.

**The ideal misses the coefficients.**  The composite `k -> T ->> k[t,t^{-1}]`
is the unit map of `k[t,t^{-1}]`, which is injective.  Since `J` is contained
in the kernel of the surjection, `J ∩ k = 0`.

So `J` is a nonzero proper two-sided ideal of `T` disjoint from the
coefficient ring, while the designated element `r = 1` is trivially full. ∎

## Scope of the counterexample

The example is degenerate in `r` — it takes `r = 1` — and that is
deliberate: it isolates the sandwich relation as the only source of
structure, so no property of `r` can be blamed.  For a general `r` the
relation `prq = 1` supplies the same one-sided inverse pattern between `pr`
and `q` and gives no reason for the corresponding defect idempotent
`1 - q(pr)` to vanish.  Nothing in this proof depends on `k` being a field
beyond making `k[t,t^{-1}]` nonzero.

What the example does **not** show is that the universal sandwich ring is
never simple for a useful choice of `R` and `r`.  It shows that simplicity
does not follow from the construction, which is what the dead route
`boone-higman-via-sandwich-ring-simplicity` assumed.
