---
rg: 2
id: spectral-range-hall-deficit-is-cutoff-monotone
kind: claim
title: Block-range Hall deficiency can only decrease as the spectral cutoff grows
---

Let `L>=0` be a positive operator on a finite-dimensional matrix space and let

```text
K_a = 1_[0,a](L) M
```

be its low-energy operator space at cutoff `a`.  Fix source/target block
decompositions and, for a source-block subset `A`, define the range-Hall
deficiency

```text
D_a(A)
 = sum_(i in A) dim(H_i)
   - sum_j dim(span{p_j T x:T in K_a, x in direct_sum_(i in A) H_i}).
```

If `0<=a<=b`, then

```text
D_a(A) >= D_b(A)                                  (SRH1)
```

for every `A`.  Consequently the optimal block-range deficiency

```text
D_a^* = max_A D_a(A)
```

is nonincreasing in `a`.

In particular, for a fixed finite Laplacian the search for a positive
range-Hall certificate only changes when the cutoff crosses an eigenvalue.
Once every source-block subset has nonpositive deficiency at one cutoff, no
larger cutoff can revive this coordinate-block certificate.
