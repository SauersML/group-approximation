---
rg: 2
id: function-field-hecke-pair-is-perfect-codense-kazhdan
kind: claim
title: SL_r(F_q[t]) < SL_r(F_q[t,1/t]) and the two-place Laurent pair are perfect Kazhdan pairs co-dense in every finite-dimensional unitary representation
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that is the general theorem, with the dyadic SL3 instance obtained from superrigidity and congruence rigidity; this verifies its hypotheses for two positive-characteristic Laurent pairs by compact recurrence along a Laurent torus, with no rigidity theorem
  stable-group-with-codense-kazhdan-subgroup: that asks for a stable host; this supplies two host candidates whose Kazhdan and co-density hypotheses are proved, and leaves stability open
  opposite-slice-contains-function-field-hecke-pair: that proves co-density in finite quotients (HP4); this upgrades it to every finite-dimensional unitary representation and draws the trace-square and HNN consequences
---

Let `q` be a prime power and `r>=3`.  Consider the pairs

```text
(i)   C=EL_r(F_q[t])=SL_r(F_q[t])      <  A=EL_r(F_q[t,1/t])=SL_r(F_q[t,1/t]),
(ii)  C=Gamma=EL_r(F_q[x_1,...,x_d])    <  A=E_pm=EL_r(F_q[x_1^(+-1),x_2^(+-1),x_3,...,x_d]),  d>=2.
```

For both pairs:

1. `C` is a finitely generated, perfect, proper Kazhdan subgroup of the
   finitely generated group `A`.

2. For every finite-dimensional unitary representation `rho` of `A`,

   ```text
   rho(A) subset closure(rho(C)),                                 (CR1)
   ```

   so `rho(C)'=rho(A)'` and `pi^C=pi^A` for every finite-dimensional unitary
   representation `pi` of `A`.

3. **Exact trace-square gap.**  Put `h=delta_12(t)` in case (i) and
   `h=delta_12(x_1x_2)` in case (ii), the torus elements of (TR1).  By
   `exact-projective-codensity-has-a-uniform-trace-square-gap` there is
   `K<infinity` such that

   ```text
   1-|tr([U,rho(h)])|^2 <= K sum_(s in S_C)(1-|tr([U,rho(s)])|^2)
   ```

   for every exact finite-dimensional unitary representation `rho` of `A`
   and every unitary `U` of the same size.

4. **Stability consequence.**  Suppose `A` is flexibly Hilbert--Schmidt
   stable, in the sense consumed by
   `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`.  Then the
   centralizer HNN group `<A,s | [s,C]=1>` is non-hyperlinear, so
   `L(C) subset L(A)` is not `RE/C`.  In case (i), the Kun--Thom double at
   the same `(q,r)` is non-hyperlinear for every `d>=3`.  In case (ii) (with
   `d>=3`), the opposite-slice double and the Kun--Thom double are
   non-hyperlinear.

The number-field pair `SL_3(Z) < SL_3(Z[1/2])` satisfies the same hypotheses
only through superrigidity and congruence rigidity.  Here a single Laurent
torus element does the work.  For the gate `(Gamma<P)` co-density fails:
`P` has finite quotients `SL_2(Z/N)` that kill `Gamma`.  So these hypotheses
live on the sub-pairs, not on the slice.

Item 4 is conditional.  Flexible HS stability of `SL_r(F_q[t,1/t])` is not
known, and a proof of it would settle `non-hyperlinear-group`.

DERIVATION
function-field-hecke-codense-recurrence-proof
