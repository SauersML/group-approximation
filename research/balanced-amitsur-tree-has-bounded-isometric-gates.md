---
rg: 2
id: balanced-amitsur-tree-has-bounded-isometric-gates
kind: claim
title: The normalized Amitsur sum has a balanced tree of bounded isometric gates
distinct_from:
  minimal-multilinear-pi-has-full-factorial-support: that proves the expanded degree-minimal identity has unavoidable square-root coefficient mass; this factors the same normalized identity through auxiliary partial sums and controls every local exact amplitude.
  rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm: that rules out a uniformly bounded constant-gap linear checker in probability-weighted norms; this supplies bounded exact witnesses and local rows but makes no rooted soundness claim.
  bounded-expander-flows-cannot-root-the-normalized-amitsur-sum: that rules out the canonical bounded-coefficient divergence proof; this uses a tree circuit and isolates the still-missing moving-root authentication.
---

ESTABLISHED.  Fix `m>=2`, put `N=m!`, and use the prefix-free Fock
substitution

```text
W_j=L_(x y^j x).
```

For `sigma in S_m`, let

```text
V_sigma=sgn(sigma) W_(sigma(1))...W_(sigma(m)).        (BAT1)
```

The `V_sigma` are isometries with pairwise orthogonal ranges.  For every
nonempty set `I subseteq S_m`, define its normalized partial sum

```text
S_I=|I|^(-1/2) sum_(sigma in I) V_sigma.               (BAT2)
```

Then every auxiliary value is again an isometry:

```text
S_I^*S_I=I.                                            (BAT3)
```

Choose a binary partition tree on `S_m` by splitting every set of size at
least two into children `I_0,I_1` whose sizes differ by at most one.  Every
internal gate obeys the exact local row

```text
S_I=sqrt(|I_0|/|I|) S_(I_0)
    +sqrt(|I_1|/|I|) S_(I_1).                         (BAT4)
```

The tree has depth `ceil(log_2 N)`.  At a nontrivial gate both squared
coefficients lie in `[1/3,2/3]`; in particular every coefficient has modulus
at most `sqrt(2/3)`, the row has arity three, and the sum of the two input
coefficient moduli is at most `sqrt(2)`.  Thus the entire expanded identity
has an exact proof assignment of operator norm one with uniformly bounded
local coefficients and logarithmic depth.

At the root,

```text
S_(S_m)=N^(-1/2) s_m(W_1,...,W_m),                    (BAT5)
```

the unit-normalized Amitsur instruction.  Conversely, in `M_n(C)` with
`m=2n`, exact satisfaction of all tree rows forces the root to equal zero by
Amitsur--Levitzki.  Hence adjoining the root normalization

```text
S_(S_m)^* S_(S_m)=I                                   (BAT6)
```

has an exact unit residual at the dimension-matched finite instruction and
an exact bounded Fock realization.

This does not supply a finite group compiler.  There are still `Theta(N)`
auxiliary gates, and a uniformly sampled local row gives the distinguished
root vanishing weight.  The gain is a precise narrowing: neither unbounded
proof values nor unbounded local coefficients are intrinsic to the Amitsur
instruction.  What remains is recursive addressing plus a nonlinear or
delocalized authentication which gives `(BAT6)` constant normalized-HS
weight without replaying the tree.

