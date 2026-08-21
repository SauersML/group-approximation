---
rg: 2
id: gowers-hatami-uniqueness-does-not-lock-nested-pauli-reservoirs
kind: claim
title: Gowers-Hatami uniqueness synchronizes fixed-level Pauli representations but not their nested multiplicity reservoirs
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that exactifies one fixed finite packet with a dimension-independent modulus; this audits compatibility along a nested extraspecial tower and identifies the surviving commutant gauge.
  rectangular-escape: that gives the abstract label-doubling/multiplicity-halving model; this realizes the escape as the canonical exact nested Pauli representation, even after perfect fixed-depth synchronization.
  common-corner-mutual-bicommutant-extraction: that asks a second scalable word algebra to expose the reservoir; this proves that flexible uniqueness for the label tower alone cannot produce that second algebra.
---

Let `E_n` be the extraspecial Pauli group with central sign `J` and `n`
Pauli pairs.  Its unique irreducible representation with `J=-1` is `pi_n`
of dimension `2^n`, and

```text
pi_(n+1)|_(E_n) ~= pi_n direct_sum pi_n.                  (GHN1)
```

Gowers--Hatami Section 7 proves the following approximate uniqueness
statement.  If two exact representations `rho,sigma:G -> U(d)` of the same
finite group are pointwise `epsilon`-close in normalized Schatten `p` norm,
then they have a common component of dimension at least

```text
(1-(2 epsilon)^p)d,                                       (GHN2)
```

implemented by a partial intertwiner within `3 epsilon` of the identity.
For `p=2`, only an `O(epsilon^2)` fraction of dimension is discarded.

This is enough to synchronize two exactifications of one **fixed-level**
Pauli table on most of the matrix space.  It does not synchronize the choice
of the next Pauli factor inside the multiplicity algebra.

### Exact coherent countermodel

Fix `N` and put

```text
H_N=(C^2)^(tensor N).
```

Represent `E_n` on the first `n` qubits:

```text
rho_n = pi_n tensor I_(2^(N-n)).                           (GHN3)
```

Then every inclusion `E_n subset E_(n+1)` is exact and coherent, while the
multiplicities obey

```text
m_n=2^(N-n)=2 m_(n+1).                                    (GHN4)
```

This is precisely rectangular escape: the label degree doubles and the
multiplicity halves with no change in ambient dimension and with zero
relator defect.

There is also complete gauge freedom in choosing the next child factor.  The
commutant of the level-`n` packet is

```text
rho_n(E_n)' = I_(2^n) tensor M_(2^(N-n)).                  (GHN5)
```

For any unitary `V` in that multiplicity algebra, define the next pair by

```text
X_(n+1)^V = V (X tensor I) V^*,
Z_(n+1)^V = V (Z tensor I) V^*.                           (GHN6)
```

The pair commutes with `rho_n(E_n)`, consists of involutions whose commutator
is the common sign `J`, and gives an exact extension to `E_(n+1)`.  Every
choice in `(GHN6)` has exactly
the same restriction to `E_n`.  Consequently the input distance to the
Gowers--Hatami uniqueness theorem at level `n` is zero, and the theorem may
return the identity intertwiner, while the chosen child `M_2` subfactor of
the reservoir is arbitrary.

The unresolved gauge at one step is the homogeneous space

```text
U(m_n) / (U(2) tensor U(m_(n+1)))                          (GHN7)
```

(up to the harmless normalizer of the tensor factors).  Restriction to
`E_n` cannot see this variable.  Separate same-level uniqueness theorems do
not impose the compatibility

```text
V_n ~= I_2 tensor V_(n+1)                                 (GHN8)
```

which a returned multiplicity reservoir would require.

### What fixed-depth exactification really gives

For any fixed depth `N`, the strongest coherent use of Gowers--Hatami is to
exactify the largest finite table `E_N` once and then restrict the resulting
exact representation down the chain.  This automatically removes all
coordinate disagreement between separately rounded levels.  Its constants
may depend on the cost of deriving that fixed table, which is acceptable in a
limit-first, depth-second argument.

But the restricted exact representation still satisfies `(GHN4)`.  Thus
perfect fixed-depth coherence does not imply same-reservoir closure; it
certifies the coherent rectangular model rather than excluding it.  For
every fixed `N` there is a zero-defect finite-dimensional model with live
sign and full carrier mass, namely `(GHN3)`.  No inequality depending only on
the nested Pauli tables can force the carrier to vanish at that depth.

### Effect of one transported copy

Approximate uniqueness can align two transported copies of the **same**
`E_n` representation when, after pulling one copy back by its named
transport, the two tables are pointwise close.  On the sign sector the
intertwiner identifies their `pi_n` factors on all but `O(epsilon^2)` mass.
It remains arbitrary on the multiplicity factor.

This does not compare an `E_n` label factor with the larger `E_(n+1)` factor
created by branching, because uniqueness applies to representations of the
same group.  Nor does it force two different extensions of the same `E_n`
table to select the same child subfactor in `(GHN5)`.  A single transported
copy therefore supplies same-level alignment, not the cross-level reservoir
return needed to defeat `(GHN4)`.

### Exact missing compatibility

A scalable-reservoir lock must add a genuinely mixed relation which compares
two extension routes and forces their relative gauge in the old commutant
`U(m_n)` to lie near the smaller commutant

```text
I_2 tensor U(m_(n+1)).                                    (GHN9)
```

Equivalently, it must close a cycle which returns to the identical
multiplicity algebra after a net label-degree expansion.  Gowers--Hatami can
then be used to exactify and align the fixed finite tables on each side of
that mixed cycle, but it cannot supply `(GHN9)` itself.

This is a rigorous no-go for the proposed shortcut, not for the reservoir
program.  The positive deliverable is the division of labor:

1. fixed-depth table coherence and same-level alignment come from one top
   exactification plus Gowers--Hatami uniqueness;
2. the only new theorem must control the relative commutant gauge around a
   mixed return cycle.

The latter is exactly the finite-matrix common-carrier compatibility absent
from the ordinary nested Clifford tower.

The analytic part of that compatibility is now closed by
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge`: once one
common relative gauge is decoded, its two commutators with the child Pauli
pair force it into the smaller reservoir with error at most the sum of the
two word errors.  The open content is therefore exposure of that common
gauge/corner, not a stronger uniqueness theorem or a larger test packet.
