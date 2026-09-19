---
rg: 2
id: hnn-collapse-reduction-proof
kind: route
title: Britton nontriviality plus exact commutation and one Cauchy-Schwarz equality prove the reduction
target: hnn-route-is-relative-commutant-collapse
requires: []
---

The claim has three assertions: the **Reduction** (`(RC1)` implies `G`
is not hyperlinear), the automatic inclusion, and the identification of
`(RC1)` with the Kun--Thom collapse template.  Throughout, `C` is a
proper subgroup, so some `a_1 in A - C` exists (every downstream
instance has `A = <C, a_1>`).

**Automatic inclusion.**  `C subseteq A` gives
`pi(A)' cap M subseteq pi(C)' cap M` by restriction of the commutation
requirement.  Nothing else is used.

**Reduction.**  Suppose `G` is hyperlinear.  By definition its regular
trace is realized in a tracial matrix ultraproduct: there is a
trace-preserving unitary representation
`pi~ : G -> U(M)`, `M = prod_U M_(d_n)`, with

```text
tau(pi~(g)) = delta_e(g)  for all g in G.                       (RED1)
```

Set `pi = pi~|_A` and `k = pi~(t)`.  Then `pi` is a trace-preserving
regular-trace representation of `A` (the regular trace of `G` restricts
on the subgroup `A` to the regular trace of `A`), and since
`[t, c] = 1` holds IN `G` for every `c in C`, the unitary `k` commutes
with `pi(C)` exactly: `k in pi(C)' cap M`.  No approximation or defect
argument is needed at this step; the relation is exact because `pi~` is
a genuine homomorphism.

Apply `(RC1)` to this `pi`: `k in pi(A)' cap M`, so `k` commutes with
`pi(a_1)`.  Hence

```text
tau(pi~([t, a_1])) = tau(k^* pi(a_1)^* k pi(a_1))
                   = tau(pi(a_1)^* pi(a_1)) = 1.                (RED2)
```

But `[t, a_1] = t^(-1) a_1^(-1) t a_1` is a nontrivial element of `G`:
`G` is the HNN extension of `A` with both associated subgroups equal to
`C` and identity edge isomorphism, and the word
`t^(-1) a_1^(-1) t a_1` contains no pinch `t^(-1) c t` or `t c t^(-1)`
with `c in C`, because its only candidate pinch letter is
`a_1^(-1) notin C`; by Britton's lemma (J. L. Britton, *The word
problem*, Ann. of Math. 77 (1963), Lemma 4) it is not the identity.
So `(RED1)` forces `tau(pi~([t, a_1])) = 0`, contradicting `(RED2)`.
Therefore `G` is not hyperlinear.

(If one prefers not to invoke `(RC1)` for every regular-trace `pi`, note
the proof only consumed `(RC1)` for the single `pi` restricted from a
hyperlinear embedding of `G`, which is how every downstream collapse
claim is quantified: over ALL trace-preserving regular-trace `pi`.)

**The identification.**  `(RC1)` and
`approximate-collapse-for-kt-compressor` are two instances of one
template: for a distinguished pair `C <= A` represented in a matrix
ultraproduct with its regular trace, the relative commutant of the
subgroup equals that of the group.  In the Kun--Thom lane the pair is
the compressed Kazhdan copy `t Gamma t^(-1) <= EL_r(F_q[x])` and the
role of co-density is played by E-normality of the compression; here
the pair is `SL_2(Z) <= SL_2(Z[1/2])` and co-density comes from the
congruence subgroup property.  This is an identification of statement
shapes, exact on both sides, not a derivation of one instance from the
other -- which is all the claim asserts.  The consequence paragraph
records that `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`
derives `(RC1)` from flexible HS-stability (its proof corrects the
restricted microstates to an exact representation and applies
co-density), so `(RC1)` is implied by, and possibly strictly weaker
than, flexible stability of `A`.
