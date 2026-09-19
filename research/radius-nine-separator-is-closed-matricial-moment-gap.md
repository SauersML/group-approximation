---
rg: 2
id: radius-nine-separator-is-closed-matricial-moment-gap
kind: claim
title: A rational radius-nine separator exists exactly when the canonical point misses the closed matricial moment body
distinct_from:
  atlas-radius-nine-trace-separator: that asserts the required gap for the atlas presentation; this proves the exact finite-dimensional dual characterization and automatic rationalization, without deciding membership.
  tracial-npa-cannot-separate-canonical-trace: that places the canonical point inside every tracial NPA relaxation; this identifies the smaller closed all-matrix-size body which must exclude it.
  matricial-radius-nine-dual-extraction: that asks for a computational hierarchy producing a replayable proof; this shows rational dual extraction is automatic after rigorous nonmembership and isolates nonmembership as the only mathematical task.
---

Choose one representative from each self-adjoint cyclic trace-word orbit of
atlas `X`-length at most nine, including the constant word, and let `N` be the
number of resulting real moment coordinates.  For a matrix unitary tuple `U`
put

```text
m_9(U) in [-1,1]^N,
D(U)=sum_(r in T_St)||r(U)-1||_2^2.
```

Let `K_9^mat` be the closure, over all matrix sizes, of

```text
{(m_9(U),D(U))} subset R^(N+1).                        (R9-DUAL-1)
```

Then `K_9^mat` is compact and convex.  If

```text
g_9=(m_9(lambda_Gamma_St),0),                          (R9-DUAL-2)
```

the following are equivalent:

1. `g_9` does not belong to `K_9^mat`.
2. There are rational radius-nine coefficients `a_w`, rational `C>0`, and
   rational `c>0` such that

   ```text
   P(U)+C D(U)>=0                    for every matrix size and tuple U,
   P(lambda_Gamma_St)<=-c.                            (R9-DUAL-3)
   ```

Thus rationality is not an additional obstruction: any strict real matricial
moment gap admits a rational certificate with the required positive relator
penalty.  Conversely every requested separator is exactly a strict separating
hyperplane for `(R9-DUAL-1)`.

Moreover,

```text
g_9 in K_9^mat
```

if and only if there is a sequence of finite-dimensional unitary tuples with
`D(U_n)->0` whose radius-nine trace moments converge to the canonical ones.
Hence failure of the radius-nine claim is a concrete truncated-microstate
statement, not failure of rational reconstruction.

The distinction from tracial NPA is exact.  The canonical group trace makes
`g_9` feasible in the corresponding closed tracial moment body, while that
body contains `K_9^mat`.  Therefore any separator from `(R9-DUAL-3)` is
genuinely matrix-only.  A finite dimension cap or a finite sample cloud gives
only an inner approximation to `K_9^mat` and cannot certify `(R9-DUAL-3)`
without an all-size outer-bound argument.

