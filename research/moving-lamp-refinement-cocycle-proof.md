---
rg: 2
id: moving-lamp-refinement-cocycle-proof
kind: route
title: Fourier-expand lamp windows and glue their partial transports
target: moving-lamp-refinement-cocycle-has-diffuse-fibers
requires:
  - elementary-abelian-regular-normalizers-have-diffuse-fibers
---

## Step 1: spectral refinement is an exact inverse system

For a finite elementary abelian group `B_E`, character orthogonality makes
the operators in `(MRC1)` pairwise orthogonal projections summing to one,
after zero projections are allowed.  If `E subset F`, then

```text
P_(E,chi)
 =2^(-|E|) sum_(b in B_E) chi(b)rho(b).
```

On the other hand, sum `P_(F,psi)` over the
`2^(|F-E|)` characters extending `chi`.  For `c in B_F`, the sum of
the coefficients `psi(c)` is zero unless `c in B_E` and is then

```text
2^(|F-E|) chi(c).
```

Substitution in `(MRC1)` gives `(MRC2)`.

If `U_g rho(b)U_g^*=rho(gbg^(-1))` for every `b in B_E`, conjugating the
Fourier sum `(MRC1)` gives `(MRC3)`.  Consequently
`u_(g,E,chi)=U_gP_(E,chi)` is a partial isometry with initial projection
`P_(E,chi)` and final projection `P_(gE,g chi)`.

Suppose covariance is also known on `B_F`.  Using `(MRC2)` twice,

```text
sum_(psi|E=chi) u_(g,F,psi)
 =sum_(psi|E=chi) U_g P_(F,psi)
 =U_g P_(E,chi)
 =u_(g,E,chi),
```

which proves `(MRC5)`.

For exact actor multiplication, use the final projection of the first
partial transport:

```text
u_(h,gE,g chi)u_(g,E,chi)
 =U_h P_(gE,g chi) U_g P_(E,chi)
 =U_h U_g P_(E,chi)
 =U_(hg)P_(E,chi)
 =u_(hg,E,chi).
```

This proves `(MRC6)`.  The objects are pairs `(E,chi)`; refinement gives
orthogonal direct-sum maps and actor elements give the partial transports.
The two displayed laws are exactly functoriality for the resulting
refinement/action groupoid.

A fiberwise change of basis replaces a transport by

```text
u_(g,E,chi)
 |-> Z_(gE,g chi) u_(g,E,chi) Z_(E,chi)^*.
```

At one coarse window, `Z_(E,chi)` may be any unitary on its restriction
fiber.  To extend to `F`, it must preserve the orthogonal splitting in
`(MRC2)` and restrict to the chosen `Z_(F,psi)`'s.  This is the precise
compatibility absent from independently chosen finite-window gauges.

## Step 2: quantitative union gluing

Write `a_x` for the nontrivial lamp at `x`.  For
`R subset S=E union F`, put `a_R=product_(x in R)a_x`.  Telescoping
products of unitaries gives

```text
||U_g rho(a_R)U_g^*-rho(a_(gR))||_2
 <=sum_(x in R) epsilon_x.                               (MRP1)
```

Every element of `B_S` is one such `a_R`.  Fourier expansion of
`P_(S,chi)`, the triangle inequality, and `(MRP1)` yield

```text
||U_g P_(S,chi)U_g^*-P_(gS,g chi)||_2
 <=2^(-|S|) sum_(R subset S) sum_(x in R) epsilon_x.
```

Each `x` occurs in exactly half of all subsets `R`, so the right side is

```text
(1/2)sum_(x in S)epsilon_x.
```

This is `(MRC7)`.  It also gives the square-summed variant

```text
||U_g P_(S,chi)U_g^*-P_(gS,g chi)||_2
 <=(sqrt(|S|)/2)(sum_(x in S)epsilon_x^2)^(1/2).         (MRP2)
```

Thus two-window covariance glues with an explicit dimension-free constant
for every fixed union.  No extra overlap condition is required beyond using
the same coordinate lamps on `E intersect F`.

## Step 3: growing overlap leaves the fiber invisible

Take the literal site action in the claim.  On
`ell^2(B_(S_m)) tensor C^(k_m)`, the lamp representation is

```text
rho_m(b)=lambda_(B_(S_m))(b) tensor 1.
```

The coordinate permutation `Q_(t,m)` implements `t` on every lamp in
`S_m`, while `F_(k_m)` commutes with the entire lamp image.  Therefore
`U_(t,m)=Q_(t,m) tensor F_(k_m)` satisfies `(MRC3)` simultaneously for
every subwindow of `S_m`.  Since `F_k^4=1` and `Q_(t,m)^4=1`, actor
multiplication is exact.  Steps 1 and 2 then make every refinement and
overlap identity exact, including those for

```text
E_m={1,...,m} times {0,1},
F_m={1,...,m} times {1,2},
E_m intersect F_m={1,...,m} times {1}.
```

The overlap dimension tends to infinity.

Every row of `U_(t,m)` has `k_m` nonzero entries of modulus
`k_m^(-1/2)`.  Hence a monomial selects total normalized overlap at most
`k_m^(-1/2)`, proving `(MRC9)`.  If `r_m=o(d_m)` dimensions are
adjoined with an arbitrary unitary block, the overlap with a monomial is at
most

```text
(d_m/sqrt(k_m)+r_m)/(d_m+r_m) -> 0.
```

Thus the padded distance tends to `sqrt(2)`.  The canonical permutation
`Q_(t,m) tensor 1` still exists, so this is a counterexample to metric
rounding and to overlap coercivity, not to spatialization itself.

Finally tensor with a separating sequence of regular finite quotients of
`SL_3(Z)`, as in
`elementary-abelian-regular-normalizers-have-diffuse-fibers`.  The actor
becomes `SL_3(Z) times C_4`, which is infinite, residually finite, and
Kazhdan; the regular quotient factor is a permutation factor and changes
none of the row-overlap estimates.  Hence property `(T)` cannot turn the
refinement identities alone into a small-gauge theorem.
