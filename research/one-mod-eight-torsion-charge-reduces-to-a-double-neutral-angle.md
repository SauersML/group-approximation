---
rg: 2
id: one-mod-eight-torsion-charge-reduces-to-a-double-neutral-angle
kind: claim
title: One-mod-eight torsion normalization reduces the padding charge to one double-neutral spectral angle
distinct_from:
  five-mod-eight-torsion-normalization-retains-a-padding-charge: that uses det v equals minus one to obtain a uniform structural-energy floor; here det v equals one and only a possible cubic determinant of u remains.
  deleted-fixed-line-first-cubic-has-explicit-positive-spectrum: that proves a uniform conjugate-pair angle before the first cubic is rounded to order three; this identifies the new conjugate-angle lemma required after that energy has been moved into the structural words.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for arbitrary mixed-packet padding; this is the exact finite-rank scalar invariant audit for one authenticated neutral Weil block.
---

Let `p=1 mod 8` and apply the standard two-triangle torsion normalization to
the compressed even-Weil tuple.  For the resulting exact
`C_2*C_3*C_3` frame and structural words `u,v` from `(ETF2)--(ETF3)`, one
has

```text
rank(u-1)<=36,           det(u) in mu_3,              (ONT1)
rank(v-1)<=46,           det(v)=1.                    (ONT2)
```

Consequently there is an exact dichotomy:

```text
det(u)!=1  =>  ||u-1||_F^2>=1/12;                    (ONT3)
det(u)=1   =>  det(u)=det(v)=1.                       (ONT4)
```

Thus every determinant-charged neutral packet already satisfies the sharp
energy-per-line ledger.  The only unresolved packet is **doubly neutral**.
In that branch neither bounded residual rank, strict nonextension, nor
conjugate-pair symmetry can yield a uniform Frobenius lower bound.  Indeed

```text
W_theta=diag(exp(i theta),exp(-i theta),1,...,1)
```

has rank at most two, determinant one, is nonidentity for `theta!=0`, and

```text
||W_theta-1||_F^2=4(1-cos(theta))->0.                 (ONT5)
```

This is a firewall on the available invariants, not an assertion that the
actual normalized Weil words realize `(ONT5)`.  To finish the
`p=1 mod 8` computation one must prove a new post-normalization spectral
statement: a nontrivial eigenangle of `u` or `v` stays uniformly away from
zero.  The pre-normalization positive first-cubic spectrum does not supply
this automatically, because the cube-root rounding sets that cubic exactly
to one and has determinant-neutral conjugate corrections.
