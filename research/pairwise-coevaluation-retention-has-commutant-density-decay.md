---
rg: 2
id: pairwise-coevaluation-retention-has-commutant-density-decay
kind: claim
title: Pairwise coevaluation retains a representation only at commutant-density weight
distinct_from:
  diagonal-retention-fusion-coefficient: that measures the total possible retained character through every fusion channel; this computes the contribution of the tempting pairwise evaluation/coevaluation channel and shows why it disappears for diffuse factor representations
  diagonal-tensor-trace-powers-forget-full-gns-tensor: that records the absence of a general recovery map from the diagonal tensor algebra; this proves that the canonical categorical recovery map itself has vanishing weight
---

Let `pi:G->U(H)` be a finite-dimensional unitary representation, `dim H=d`,
and put

```text
c=dim End_G(H).
```

In the odd mixed tensor representation

```text
R_n=pi^(tensor(n+1)) tensor conjugate(pi)^(tensor n),
```

pair each of the last `n` copies of `pi` with a conjugate copy.  The invariant
space of one paired factor is

```text
K=(H tensor conjugate(H))^G ~= End_G(H),
```

so the resulting pairwise-coevaluation carrier is

```text
H tensor K^(tensor n).
```

It consists of `c^n` copies of `pi`, but its normalized trace weight inside
`R_n` is exactly

```text
               d c^n
w_n = ------------------------- = (c/d^2)^n.            (PCR1)
             d^(2n+1)
```

This formula already includes arbitrary representation multiplicity.  If

```text
pi = direct_sum_alpha (V_alpha tensor C^(m_alpha)),
```

then `c=sum_alpha m_alpha^2`.  In particular, an `m`-fold amplification of
one irreducible representation of degree `r` has

```text
c/d^2=1/r^2,                                             (PCR2)
```

independently of `m`.  For each fixed nonscalar `pi`, `c<d^2`, so the
pairwise carrier decays exponentially.  Fixed density in a varying family
would require

```text
n(1-c/d^2)=O(1),                                         (PCR3)
```

meaning that the adjoint representation is asymptotically almost entirely
fixed; it is not a dimension-free fusion mechanism.

There is an even sharper diffuse-factor obstruction.  If `pi(G)''=M` is a
diffuse finite factor in its tracial GNS representation on `L^2(M)`, then

```text
(L^2(M) tensor conjugate(L^2(M)))^G
 ~= M' intersection S_2(L^2(M)) = {0}.                  (PCR4)
```

Indeed, the tensor product identifies with Hilbert--Schmidt operators and
the invariant vectors with Hilbert--Schmidt intertwiners.  A nonzero compact
operator in `M'` would have a nonzero finite-rank spectral projection in
`M'`, giving a nonzero finite-dimensional normal representation of the
diffuse factor `M`; factoriality makes such a representation faithful, which
is impossible.  Thus the formal infinite-dimensional coevaluation vector is
not a Hilbert-space vector at all.

Therefore the familiar finite-dimensional cancellation
`pi -> pi tensor pi tensor conjugate(pi)` cannot retain a non-CE II1-factor
character.  Any successful fixed-density recurrence must use genuinely new
global fusion channels, and those channels remain subject to the exact
Rayleigh test in `diagonal-retention-fusion-coefficient`.
