---
rg: 2
id: trace-conditioned-kleene-diagonal-proof
kind: route
title: Add strict finite moment tests to the self-witness search
target: trace-conditioned-dimension-matched-kleene-diagonal
requires: []
---

Use the recursion theorem exactly as in the dimension-matched diagonal.  The
fixed-point program computes its own compiler output and searches a dense
computable family of algebraic unitary tuples for strict versions of every
inequality in `(TDM2)`, with the defect threshold decreased and the marked
threshold increased slightly.  If it halts, it prints the witness dimension;
halting soundness then contradicts that same witness.  Hence it does not halt,
so the compiled word is nontrivial and the target moments are its canonical
trace moments.

If the group were hyperlinear, canonical-trace microstates would eventually
satisfy the relators, keep the nontrivial word arbitrarily close to
`sqrt(2)` from the identity, and approximate all finitely many target moments.
Strictness and density make the search halt, a contradiction.

For an exact representation `rho` of a fixed finite subgroup `K`, character
orthogonality gives

```text
n_lambda=(1/|K|) sum_(g in K) conjugate(chi_lambda(g)) Tr(rho(g)).
```

Thus trace tests `|tr(rho(g))|<=eta` for `g!=1` force the Hilbert-space
fraction `p_lambda=d_lambda n_lambda/d` to satisfy

```text
|p_lambda-d_lambda^2/|K||
 <=(d_lambda/|K|) sum_(g!=1)|chi_lambda(g)| eta.         (1)
```

Fixed finite-group exactification transfers the same conclusion, with a
fixed additional vanishing error, to approximate packet tables.
