# Whole-module Kazhdan and mixed-word audit — 2026-08-21

## Outcome

Two tempting shortcuts to the infinite-character word-energy interface can
be ruled out exactly.

First, the natural Hilbert--Schmidt intertwiner construction uses the left
and right representations

```text
m |-> rho(s m), rho(m),
a |-> pi(s a s^-1), pi(a).
```

These define a representation of the free product `M*A`.  They descend to
`M rtimes A` exactly when **all** module covariance identities already hold.
The defect on the mixed relator indexed by `(a,m)` is the covariance defect
for that same `m`.  Hence the relative Kazhdan projection cannot be invoked
before the whole-module gate; doing so assumes the missing conclusion.

Second, allowing noncommutative mixed words does not help if their domains
come only from finitely many diagonal module evaluations.  Two characters
which agree on all tested elements make that entire algebra scalar on their
two-block carrier.  Exchanging the blocks then leaves every finite
conjugation-balanced mixed word unchanged while retaining fine transport
energy `2`.

## Surviving positive target

The only surviving property-`(T)` mechanism must therefore be a genuine
**lamp-coupled actor correction theorem**:

1. use the finite actor presentation and native lamp relations to correct
   the free-product left-right action to an actual semidirect-product
   representation, with a dimension-independent modulus;
2. only then apply the relative Kazhdan projection to obtain whole-module
   intertwining.

Equivalently, a successful mixed square function must authenticate
non-diagonal domains through the other actor generators.  Repackaging a
finite family of diagonal module words around one transporter remains
character-blind.

This is strictly narrower than the pre-existing finite spectral-probe and
virtually-free residual fences: it identifies the exact semidirect relator
where the Kazhdan bimodule fails and extends the marginal blindness to
finite conjugation-balanced noncommutative words.
