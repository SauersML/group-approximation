---
rg: 2
id: stw99-xciv-local-prime-dimension-drop-equivalence-proof
kind: route
title: Diagonalize local prime blocks and invoke the compatibility-free dimension-drop absorption criterion
target: stw99-xciv-separable-zstability-iff-local-prime-dimension-drops
requires:
  - stw99-xciv-separable-zstability-iff-local-norm-central-z
---

We first isolate the standard absorption input.  Write `Z` as the closure of
an increasing union of nuclear prime dimension-drop algebras

```text
D_i=Z_(p_i,q_i),             gcd(p_i,q_i)=1.
```

Toms--Winter's dimension-drop absorption criterion says that if `C` is
separable and unital and each `D_i` admits a unital homomorphism into
`C_infinity intersect C'`, then `C` is `Z`-stable.  The homomorphisms for
different `i` need not be compatible: compatibility is produced by the
diagonal lifting argument in that criterion.

Suppose first that condition 1 holds.  The already established local
norm-central `Z` equivalence gives, for finite `F subset B`, a unital
homomorphism `phi:Z->B` which is as norm-central on `F` as desired on any
prescribed finite subset of `Z`.  Every prime dimension-drop algebra embeds
unitally into `Z`; fix `eta_k:I_k->Z`.  Applying the local `Z` criterion to
`eta_k(H_k)` and composing gives

```text
psi=phi compose eta_k:I_k->B,
```

with the required estimates.

Conversely assume condition 2 and fix a norm-separable set `S subset B`.
Set `C_0=C*(S,1)`.  Having constructed separable unital
`C_0 subset ... subset C_n`, choose a countable dense sequence in the unit
ball of each `C_j`.  At stage `n`, test the first `n` elements of each of the
first `n` dense sequences.  Choose a sequence `(k_n)` in which every integer
`k>=2` occurs infinitely often, and use condition 2 to obtain a unital

```text
psi_n:I_(k_n)->B
```

whose commutators with that finite test set on `H_(k_n)` are less than
`1/n`.  Put

```text
C_(n+1)=C*(C_n,psi_n(I_(k_n))),
C=closure(union_n C_n).
```

Then `C` is separable, unital, and contains `S`.  Fix `k`, and pass to the
subsequence `n(1)<n(2)<...` on which `k_n=k`.  Coordinatewise application
gives a unital homomorphism

```text
Psi_k:I_k->C_infinity,       Psi_k(x)=[(psi_(n(j))(x))_j].
```

For every fixed element of every `C_m`, the diagonal tests make the
commutators with `Psi_k(h)` vanish for each `h in H_k`.  Density extends this
to all of `C`; since `H_k` generates `I_k`, the commutant is a C\*-algebra,
and hence

```text
Psi_k:I_k->C_infinity intersect C'
```

is unital.

It remains only to match these blocks to the fixed model of `Z`.  If
`D_i=Z_(p,q)`, choose positive integers `r,s` with

```text
s q-r p=1
```

(add a sufficiently large multiple of `(q,p)` to any Bezout solution).
Amplifying the two matrix coordinates gives a unital homomorphism

```text
Z_(p,q) -> Z_(r p,s q)=I_(r p).
```

Composing with `Psi_(r p)` gives a unital homomorphism
`D_i->C_infinity intersect C'` for every `i`.  The absorption criterion now
gives `C~=C tensor Z`.  Thus `C` is the required separable `Z`-stable hull of
the original set `S`.

Finally, the displayed norm-gap statement in the claim is exactly the
logical negation of condition 2: failure supplies one triple
`(F,k,delta)`, and such a triple plainly prevents condition 2.  No
compactness or attainment assertion is used.
