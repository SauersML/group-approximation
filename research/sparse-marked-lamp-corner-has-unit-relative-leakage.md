---
rg: 2
id: sparse-marked-lamp-corner-has-unit-relative-leakage
kind: claim
title: A sparse visible two-lamp corner can retain unit character leakage
distinct_from:
  pointwise-lamp-covariance-has-half-mass-leak: that uses two-dimensional lifts and a moving character frontier, but its fixed corona character is total parity and its displayed two-atom leakage has ambient mass one half; this produces a fixed two-lamp spectral projection of constant nonzero rank in growing matrices, puts every moving character in a trivial-stabilizer Schreier orbit, and proves that leakage normalized by the marked corner is exactly one.
  lamp-character-transport-bounds-schreier-dirichlet: that converts an already controlled ambient leakage into a classical Dirichlet bound; this shows that dividing its vanishing ambient quantities by the rank of a sparse marked corner does not manufacture the missing leakage control.
  norm-corona-sparse-global-character-atom: that builds a sparse character atom in a norm corona; this couples three such atoms to an exact finite actor representation and makes the full character labels escape every prescribed actor target while all fixed lamp covariance relations stabilize.
---

**ESTABLISHED.**  Let `A = F(a,b)`, let

```text
M = direct_sum_A C_2,
Gamma = M semidirect A,
w = m_e m_a.
```

There are dimensions `d_n -> infinity`, exact representations

```text
rho_n : M -> U(d_n),
U_n   : A -> U(d_n),
```

and rank-two projections

```text
p_n = (1-rho_n(w))/2
```

with the following properties.

1. For every fixed `g in A` and `m in M`, the covariance identity

   ```text
   U_n(g) rho_n(m) U_n(g)^* = rho_n(g.m)                       (SLC1)
   ```

   holds for all sufficiently large `n`.  Hence
   `sigma_n(m,g)=rho_n(m)U_n(g)` is a pointwise operator-norm asymptotic
   representation of `Gamma` and defines a norm-corona homomorphism.
2. `rank(p_n)=2`, so `tr_(d_n)(p_n)=2/d_n -> 0`, but
   `p=[(p_n)]` is a nonzero projection in the norm corona and

   ```text
   ||[(rho_n(w))]-1|| = 2.
   ```

   Thus the fixed two-lamp mark remains operator-norm visible on a genuinely
   sparse corner.
3. The nontrivial part of the joint character PVM of `rho_n` consists of
   three rank-one atoms.  Every one of their full lamp characters has trivial
   stabilizer in `A`; consequently its dual orbit is a regular `F(a,b)`
   Schreier orbit and has the uniform elementary gap

   ```text
   sum_(s in {a,a^-1,b,b^-1}) ||h-s.h||_2^2
     >= (8-4 sqrt(3)) ||h||_2^2.                               (SLC2)
   ```
4. Nevertheless, for every `s in {a,a^-1,b,b^-1}`, every nontrivial
   character atom misses its prescribed `s`-translate.  In particular, if
   `L_(s,n)(p_n)` denotes `(CTL1)` summed only over the two atoms below
   `p_n`, then

   ```text
   L_(s,n)(p_n) = tr_(d_n)(p_n) = 2/d_n,
   L_(s,n)(p_n) / tr_(d_n)(p_n) = 1.                            (SLC3)
   ```

The ambient leakage in `(SLC3)` tends to zero, exactly as pointwise corona
covariance allows, while the marked-corner-normalized leakage is maximal.
Equal amplification, subsequences and adding arbitrary trivial spectator
blocks do not change the ratio.

**Consequence.**  Pointwise operator-norm covariance plus nonzero `K_0`
rank of a sparse visible lamp projection does not yield a corner-normalized
character-transport theorem, even when the selected coordinate characters
all lie in Schreier orbits with one common positive gap.  The atomic
Schreier inequality can consume a relative leakage estimate, but neither
corner normalization nor the rank germ supplies that estimate.  A positive
Tarski-lamp argument must authenticate a globally compatible character lift
by additional whole-module information; it cannot recover it from pointwise
covariance after passing to the sparse corner.

