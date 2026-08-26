---
rg: 2
id: llp-makes-hyperlinear-traces-amenable
kind: claim
title: LLP makes every hyperlinear trace amenable
distinct_from:
  llp-regular-dominating-completion-forces-nonhyperlinear: that is the published group-representation-completion criterion requiring a regular-dominating nonamenable representation; this is the underlying trace-level lifting statement for an arbitrary unital C-star algebra.
  property-t-cstar-amenable-trace-forces-fd-quotient: that turns an already amenable trace on a property-T algebra into a finite-dimensional quotient; this turns a hyperlinear trace into an amenable one using LLP and no rigidity hypothesis.
---

**ESTABLISHED GENERAL LEMMA.**  Let `A` be a unital C-star algebra with LLP,
and let `tau` be a hyperlinear trace on `A`.  Then `tau` is amenable.

Hyperlinearity supplies a trace-preserving star-homomorphism

```text
pi:(A,tau) -> product_omega (M_(d_k),tr_(d_k)).         (LHA1)
```

Realize the target as the C-star quotient of `product_k M_(d_k)` by the
closed ideal of bounded sequences whose normalized two-norm tends to zero
along `omega`.

For each finite-dimensional operator system `E subset A` containing a
chosen finite set and its products, LLP gives a ucp local lift

```text
theta_E:E -> product_k M_(d_k)                         (LHA2)
```

of `pi|_E`.  Its coordinate maps extend ucp from `E` to `A`.  Because the
quotient image is multiplicative, for `x,y` in the chosen finite set,

```text
||theta_(E,k)(xy)-theta_(E,k)(x)theta_(E,k)(y)||_(2,tr)
 ->_omega 0,                                           (LHA3)
```

and trace preservation gives

```text
tr_(d_k)(theta_(E,k)(x)) ->_omega tau(x).              (LHA4)
```

Choose increasing finite systems and diagonal coordinates in the
corresponding ultrafilter-large sets.  The resulting ucp maps
`phi_j:A->M_(n_j)` recover `tau` and are asymptotically multiplicative in
normalized two-norm.  This is the standard ucp-microstate characterization
of an amenable trace.  Hence every hyperlinear trace on an LLP algebra is
amenable.

DERIVATION
llp-local-lifts-hyperlinear-trace-proof
