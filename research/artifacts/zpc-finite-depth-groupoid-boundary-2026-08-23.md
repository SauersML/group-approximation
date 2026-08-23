# Finite verifier depth does not close the readable translate groupoid

For a finite readable Boolean algebra `D_0` and unreadable generator set `S`,
put

```text
D_n = join_{|w|<=n} w D_0 w^(-1).
```

The exact boundary identity is:

```text
D_n is S-normalized  <=>  D_n=D_(n+1)
                       <=>  D_n=D_infinity.
```

Thus an ordinary group presentation cannot retain only the translates used
by a bounded-depth verifier while making the unreadable generators monomial
on one finite atom set.  Global invertibility and multiplication force the
boundary arrows to continue to every word depth.  Closing them artificially
adds return cycles/holonomy not present in the source action.

The obstruction occurs in exact perfect ZPC actions: take two Bernoulli
coordinate reflections whose product is the bilateral shift, a central free
fiber flip `J`, and a remote readable involution whose flip bit is the
zeroth Bernoulli coordinate.  All named game variables remain involutions;
the readable translates generate every coordinate bit, while all finitely
required local ZPC commutators can be made exact.

Therefore finite verifier depth alone cannot groupify the perfect ZPC-IRS
strategy without freezing.  The special gap witness would need an additional
finite-orbit or invariant-fiber theorem, or a nonmonomial trace-promotion
construction.
