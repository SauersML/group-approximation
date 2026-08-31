---
rg: 2
id: bcv-arbitrary-perfect-halt-readable-diagonal-proof
kind: route
title: Invert the BCV fixed point along every perfect strategy and diagonalize its forced Pauli packets
target: bcv-no-computable-perfect-halt-readable-bound
requires:
  - bcv-every-perfect-compression-amplifies-readable-closure
  - bcv-perfect-compression-backward-amplification-proof
---

Let `lambda=lambda(M)>0` be the polynomial-time computable integer supplied
by BCV Lemma 2.61. It makes the halting verifier
`V=V_(M,lambda)` `lambda`-bounded. Let `C` be the construction
constant from Theorem 2.53 and define `T_j` and `h` as in `(NHB1)`.

## 1. Exact fixed-point levels

For every `j<h` one has `T_j<N`, so `M` has not halted in
`T_j` steps. Clause 2 of BCV Lemma 2.59 is equality of tailored games,
not merely equality of values:

```text
V_(T_j) = Compress(V,lambda)_(T_j).                       (NHP1)
```

Since `T_(j+1)=2^(T_j)`, the exact backward compression theorem applied
at `n=T_j` decodes a perfect strategy at level `T_j` to one at level
`T_(j+1)`.

There is one extra hypothesis in the generic backward theorem: to pass from
the decoded double cover to `V_(T_(j+1))`, its supported nonzero-answer
graph must be bipartite. For this fixed point the hypothesis follows from
the printed sampler identities, at every level, as follows.

## 2. The support handoff is bipartite at every level

Clause 1 of Lemma 2.59 says that, for every integer `m`, whether or not
`M` has halted by then, the underlying graph, both answer-length
functions, and the edge distribution of

```text
V_m  and  Compress(V,lambda)_m
```

are the same. Theorems 6.8 and 7.1 identify the latter sampler exactly as

```text
(DeType(Anchor(V^(2)_m)))^(tensor K(m)).                  (NHP2)
```

Definition 4.40 describes the two output ranges of one `DeType` factor.
A supported non-anchor left endpoint is an A-copy

```text
(enc(t),0,1_t,x),
```

and a supported non-anchor right endpoint is a B-copy

```text
(0,1_(t'),enc(t'),y).
```

These ranges are disjoint because the A-copy has nonzero first type
indicator and the B-copy has zero there. An A-player anchor has the form

```text
(u_type,u_neighbors,0,0,0),
```

whereas a B-player anchor has the form

```text
(0,0,v_type,v_neighbors,0).
```

Their ranges intersect only in the all-zero vertex `o`. Definition 4.40
assigns answer length zero to every anchor and autoaccepts every sampled
edge incident to one. Cross intersections between a copy and an
opposite-player anchor are impossible for the same type-indicator reason.

In the tensor sampler, every left endpoint is a tuple of left-range
vertices and every right endpoint a tuple of right-range vertices. Hence
the two endpoint ranges intersect only in `(o,...,o)`, whose total answer
length is zero. Removing that harmless zero-answer vertex leaves a genuine
bipartition of the entire supported graph of `(NHP2)`. By Lemma 2.59
clause 1, the same is true for every `V_m`, in particular for
`m=T_(j+1)`. Thus opposite-sheet selection in the exact Question
Reduction decoder is valid at every recursive handoff. No synchronization
loop or unprinted cross-player block identity is being assumed.

## 3. Iterate the readable inclusions

Start with an arbitrary attained-perfect finite-dimensional
signed-permutation ZPC strategy `S_0` for `V_(T_0)=G_M`. For every
`0<=j<h`, use `(NHP1)` and the full backward compression theorem.
The support calculation above supplies a perfect ZPC strategy `S_(j+1)`
for `V_(T_(j+1))` and a monomial unitary `W_j` such that

```text
W_j D_infinity(S_j) W_j^*
  contains
  ell^infinity(F_2^(k_j)) tensor D_infinity(S_(j+1)),
k_j=2^(lambda T_j).                                      (NHP3)
```

All wrapper inverses are restrictions, marginalizations, or exact
coarse-grainings in the same matrix algebra; the only basis change is the
displayed monomial Pauli normal form. Therefore `(NHP3)` has the required
readable/unreadable ZPC typing and can be composed at successive levels.

For a finite-dimensional algebra,

```text
dim(ell^infinity(F_2^(k_j)) tensor D_infinity(S_(j+1)))
  =2^(k_j) dim D_infinity(S_(j+1)).
```

Taking dimensions in `(NHP3)` and multiplying for `j=0,...,h-1`
gives

```text
dim D_infinity(S_0)
 >= product_(0<=j<h) 2^(k_j) dim D_infinity(S_h)
 >= product_(0<=j<h) 2^(2^(lambda T_j))
 >= 2^h.                                                 (NHP4)
```

The last inequality uses only `lambda>0`, `T_j>=C>=1`, and hence
`k_j>=1`. If `h=0`, the product is empty and the assertion is the
tautological lower bound one.

## 4. A computable bound would decide HALT

Assume for contradiction that a total computable `B` satisfies
`(NHB3)`. On input `M`, compute

```text
r=floor(log_2(max(1,B(M))))+1,
```

then compute the finite tower value `T_r` and simulate `M` for exactly
`T_r` steps. If it halts, answer HALT.

Suppose it has not halted by `T_r` but later first halts at time `N`.
Then `N>T_r`, so `h>r`. Equation `(NHP4)` applies to every perfect
strategy for `G_M` and yields

```text
dim D_infinity(S) >= 2^h > B(M).
```

That contradicts the perfect strategy promised by `(NHB3)`. Therefore
failure to halt by `T_r` certifies that `M` never halts, and the
procedure decides the halting problem. No such total computable `B`
exists.

All parameter conditions used above are explicit: `C` is the fixed
positive threshold of Compression; `T_j>=C` makes every wrapper defined;
`K(T_j)>=1`; `lambda(M)` is a computable positive integer; all sampler
claims concern positive-weight support; and the strategies are attained,
perfect, and finite-dimensional. Unsupported formal questions can be
filled with trivial PVMs and do not affect value, ZPC, or readable closure.
