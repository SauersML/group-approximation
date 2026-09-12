---
rg: 2
id: central-packet-sign-supplies-marked-carrier
kind: claim
title: A fixed packet's central sign supplies the marked carrier without Boone self-reference
artifacts:
  - research/artifacts/meta-recursive-qca-audit-2026-08-22.md
distinct_from:
  fanizza-boone-mark-carrier-interface: that asks for a uniform machine-indexed mark coupled to the published signal; this applies to one fixed non-CE BCS groupification and uses its existing central packet sign.
  marked-hs-separation-forces-spectral-density: that treats an arbitrary marked unitary by a threshold carrier; this rounds an approximate central involution and obtains an approximately reducing sign corner.
---

Let `Gamma=<S|R>` contain a central involution `J`, and suppose `Gamma` has an
exact unitary representation `pi` with `pi(J)=-I`.  Then `J!=1` in `Gamma`.
For a finite-dimensional unitary tuple with total squared relator energy `E`,
write `W=U(J)`.  There is a self-adjoint involution `Z` such that

```text
||W-Z||_2 <= 3 sqrt(E).                                (CSM1)
```

If `||W-I||_2>=alpha` and `sqrt(E)<=alpha/6`, its negative projection
`Q=(I-Z)/2` satisfies

```text
tau(Q)>=alpha^2/16.                                   (CSM2)
```

Moreover every centrality relator gives, for each named generator `s`,

```text
||[Q,U(s)]||_2 <= 4 sqrt(E).                           (CSM3)
```

Thus a fixed central packet sign gives a positive-density approximately
reducing carrier directly.  If a groupification proves a uniform HS energy
floor on every such `J=-1` carrier and preserves one exact representation
with `J=-I`, the resulting fixed finitely presented group is nonhyperlinear.
No Turing machine, Boone word, or runtime-independent terminal comparison is
needed for this existence route.

For the isolated involution relator there is a sharper one-line estimate.
If `W` is unitary and `||W^2-I||_2<=epsilon`, round each eigenvalue to the
nearest sign to obtain an exact self-adjoint involution `Z`. Since

```text
min(|z-1|,|z+1|)<=|z^2-1|                 (|z|=1),
```

one has `||W-Z||_2<=epsilon`. Hence, for `Q=(I-Z)/2` and
`||W-I||_2>=alpha`,

```text
tau(Q)=||Z-I||_2^2/4 >= (alpha-epsilon)^2/4.           (CSM4)
```

In canonical microstates of a group with `J!=1`, the canonical trace gives
`tr(J)->0`, so `||J-I||_2->sqrt(2)` and the rounded negative sector has
asymptotic density `1/2`.
