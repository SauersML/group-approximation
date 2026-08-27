---
rg: 2
id: sl3-amalgamated-free-enemy-outlier-proof
kind: route
title: The subgroup-indicator commutator moment activates the unbalanced torus inequality
target: sl3-amalgamated-free-enemies-are-ambient-extension-outliers
requires:
  - unbalanced-torus-extracts-near-central-denominator-coordinate
---

Write `B=pi(L(C))`.  First compute the one mixed moment which is special
to the HNN enemy.  Since `h` is not in `C`,

```text
E_B(pi(h))=E_B(pi(h)^*)=0.
```

Also `E_B(k)=E_B(k^*)=0`.  Hence

```text
k pi(h) k^* pi(h)^*
```

is an alternating product of centred letters from `W^*(B,k)` and
`pi(L(A))`.  Amalgamated freeness gives

```text
E_B(k pi(h) k^* pi(h)^*)=0,
tau([k,pi(h)])=0.                                      (AEO2)
```

(Changing from `k^* pi(h) k pi(h)^*` to the displayed commutator changes
nothing: both are centred alternating words.)  Thus for any representing
sequences,

```text
1-|tr([K_n,H_n])|^2 -> 1.                              (AEO3)
```

Meanwhile `k in B'` implies, for every fixed `s in S`,

```text
||[K_n,X_(n,s)]-I||_2 -> 0.                            (AEO4)
```

Suppose `(AEO1)` failed.  After passing to an ultrafilter-large subsequence
there would be exact representations `sigma_n:A->U(d_n)` with

```text
xi_n=max_(s in S)||X_(n,s)-sigma_n(s)||_2 -> 0.         (AEO5)
```

The actor presentation defects `delta_n` tend to zero.  Fixed-word
telescoping transfers `(AEO4)` across `(AEO5)`, so the projective lattice
energy of `K_n` relative to `sigma_n|C` tends to zero.  Apply the
perturbative conclusion `(NCD5)` of
`unbalanced-torus-extracts-near-central-denominator-coordinate`, with
`U=K_n`.  It yields

```text
1-|tr([K_n,H_n])|^2 <= Omega(delta_n+xi_n+q_n) -> 0,    (AEO6)
```

contradicting `(AEO3)`.  Therefore the ultralimit of the infimum in
`(AEO1)` is positive.  Equivalently, if no such positive epsilon existed,
choosing a representation within `1/n` of the infimum on successive
ultrafilter-large sets would produce `(AEO5)` and the same contradiction.
