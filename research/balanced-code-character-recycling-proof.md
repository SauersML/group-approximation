---
rg: 2
id: balanced-code-character-recycling-proof
kind: route
title: Kill a fixed fraction of swap pairs at every balanced level
target: balanced-low-gap-cut-trees-can-recycle-a-code-character
requires: []
---

Fix an integer `n` with `1/n<=rho`.  Take `N` sufficiently divisible and
large and work on `C^(2N)`.  Let

```text
Q=directSum_(a=1)^N [[0,1],[1,0]],
B_i=Q^(c_i).
```

Every `B_i` is a reflection and the tuple commutes.  If `h in C^perp` is a
parity check, then

```text
product_i B_i^(h_i)=Q^(<h,c>)=I.
```

Hence all code parity and complete-pair relations are exact.

Build the tree recursively.  At a current node, the compressed `Q` is a
direct sum of active two-dimensional swaps and zero scalar lines.  Choose a
half-dimensional child projection `p` as follows.  Split exactly a `1/n`
fraction of the active swaps, putting one coordinate line in each child;
allocate the remaining active swaps wholly and equally between the two
children; and divide the already-zero scalar lines equally.  Divisibility
is ensured by the initial amplification.  Put

```text
x=2p-e.
```

Then `x` is a selfadjoint unitary in the node corner, has corner trace zero,
and `p=1_[0,infinity)(x)`.  Only the split active swaps contribute to its
commutator.  Their fraction of the node dimension is at most `1/n`, so

```text
||[eQe,x]||_(2,e)^2 <=4/n.
```

Since `B_i=I` off `supp(c)` and `B_i=Q` on `supp(c)`, averaging gives
`(BRC1)`.  If the coarea normalization uses the unaveraged generator sum,
start with `1/n<=rho/L` instead.

Repeat this split simultaneously in every current node.  After `k` levels,
the fraction of active swaps is `(1-1/n)^k`.  Choose `k` so large that this
is at most `1/n`, and on the last level split every remaining active swap.
That final cut still has relative boundary at most `1/n`.  Extra scalar
amplification makes all half-dimension allocations integral.  Thus every
terminal leaf contains only zero scalar compressions of `Q`, proving
`(BRC2)`.

For `c_i=1`, therefore, `O_i=Q`; for `c_i=0`, `O_i=0`.  Since `Q^2=I`,
the identities `(BRC3)` follow immediately.  Finally
`sgn(Phi_F(B_i))=I` for every `i`, so the terminal signed tuple is the
trivial code character and has zero balanced relation energy.  Finally,
for every unitary `U`, the signed coordinate stays `UIU*=I`; on
`supp(c)`,

```text
||Q-I||_2^2=2-2 Re tau(Q)=2.
```

Averaging over the support of `c` proves `(BRC4)`.
