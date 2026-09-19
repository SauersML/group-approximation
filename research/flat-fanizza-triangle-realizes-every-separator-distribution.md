---
rg: 2
id: flat-fanizza-triangle-realizes-every-separator-distribution
kind: claim
title: The abstract native flat triangle has an exact finite model for every rational separator distribution
distinct_from:
  fanizza-native-additive-incidence-is-one-triangle: that proves pointwise extension of each of the eight separator assignments; this takes arbitrary mixtures and derives the no-go for marginal/rank-only trace-cyclic returns.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that balances representation restrictions abstractly; this constructs a simultaneous classical model of the actual four native truth tables.
  trace-cyclic-triangle-balances-independent-return-gauges: that shows a rank-balancing chord is sufficient once two proper returns exist; this proves that native truth tables and separator rank balance cannot construct those returns.
---

Let

```text
s=(O_Q,O_P,Z_tilde) in {+1,-1}^3                    (FFT1)
```

be the three separator signs of the native Fanizza triangle.  For every
rational probability distribution `mu` on the eight values of `s`, there is
an exact finite-dimensional diagonal model of all four abstract native
context tables whose joint separator distribution is exactly `mu`.  Here,
as in the incidence audit, the prescribed machine-word occurrences are
temporarily treated as context signs; the conclusion deliberately does not
claim that the native machine relations also hold.

Indeed, `fanizza-native-additive-incidence-is-one-triangle` constructs, for
each `s`, one simultaneous satisfying assignment `a(s)` of all four context
truth tables.  Choose a common denominator `N` for `mu`, take `N mu(s)`
copies of the one-dimensional assignment `a(s)`, and form their direct sum.
All local predicates are satisfied exactly.  The occurrences of every shared
separator are literally the same diagonal involution, not merely equal in
trace.

Consequently no proposed native-triangle actuator can obtain either proper
return `(TCT2)` or `(TCT3)` solely from:

- the four finite context truth tables;
- equality, conjugacy, or bistochastic matching of separator marginals;
- any finite graph of finite packet restriction tables placed on those
  marginals; or
- a bounded equality/dimension-expander cloud which only repeats the same
  separator tests.

Every such construction has the exact diagonal model above (and its common
amplifications).  An independent finite D8 packet may be tensored onto it,
leaving the D8 projection `H` positive while every marginal/incidence check
remains exact.

Thus the third rank-balancing edge of
`trace-cyclic-triangle-balances-independent-return-gauges` is genuinely the
easy part.  The two proper returns must use a noncommutative relation among
the **prescribed native machine words**—for example the guarded recurrence
involving `P,X_tilde,U,Z_tilde,J`—which the abstract separator assignments
do not see.  A two-matching or dimension-expander sampler is relevant only
if it acts on those native multiplicity coordinates and enforces a
noncommuting phase/return law; expanding copies of the flat Boolean
incidence cannot help.
