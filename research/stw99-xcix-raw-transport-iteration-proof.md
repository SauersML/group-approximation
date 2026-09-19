---
rg: 2
id: stw99-xcix-raw-transport-iteration-proof
kind: route
title: Iterate the exact commutator perturbation inequality and audit its sharp Lipschitz constants
target: stw99-xcix-raw-transport-iteration
requires: []
---

Write `S_j=A` for even `j` and `S_j=B` for odd `j`.  Since
`d(A,B)<gamma`, both near inclusions `A subset_gamma B` and
`B subset_gamma A` hold.  Corollary 4.7 of
[Perturbations of nuclear C*-algebras](https://arxiv.org/abs/0910.4953)
therefore transports `psi_j:D -> S_j` to an embedding
`psi_(j+1):D -> S_(j+1)` satisfying, on `Y`,

```text
||psi_(j+1)(y)-psi_j(y)|| < 152 sqrt(gamma).
```

The first application ensures that both sides admit an embedding of `D`, so
the argument can be alternated for any finite number of steps.

Let `x_i^j=a_i` on even steps and `x_i^j=b_i` on odd steps.  For every `i`
and `y in Y`, expand

```text
[psi_(j+1)(y),x_i^(j+1)]
 = [psi_(j+1)(y)-psi_j(y),x_i^(j+1)]
   + [psi_j(y),x_i^(j+1)-x_i^j]
   + [psi_j(y),x_i^j].
```

All displayed elements except the differences are contractions.  The norm
inequality `||[r,s]|| <= 2||r||||s||` gives

```text
||[psi_(j+1)(y),x_i^(j+1)]||
 < ||[psi_j(y),x_i^j]|| + 304 sqrt(gamma) + 2 gamma.
```

Taking maxima over the finite index sets proves
`e_(j+1)<e_j+Delta`.  Induction gives `e_n<e_0+n Delta`.  Equivalently, the
worst-case scalar update certified by these estimates is
`T(e)=e+Delta`, and `T^n(e)=e+n Delta`; no iterate is a contraction when
`gamma>0`.

For completeness, the constants `2` cannot be reduced in an argument that
uses only norms of arbitrary contractions.  In `M_2`, let

```text
x = diag(1,-1),       r = delta e_12,       0 < delta <= 1.
```

Then `||x||=1`, `||r||=delta`, and `||[r,x]||=2 delta`.  This proves
sharpness for perturbing the first commutator entry.  Interchanging the two
entries proves sharpness for perturbing the second.  These examples do not
assert sharpness inside the restricted class of pairs of transported
strongly self-absorbing embeddings; they isolate the exact trust boundary of
the raw norm-and-triangle-inequality method.
