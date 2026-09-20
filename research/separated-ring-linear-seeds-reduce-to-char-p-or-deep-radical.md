---
rg: 2
id: separated-ring-linear-seeds-reduce-to-char-p-or-deep-radical
kind: claim
title: A torsion-free acylindrically hyperbolic MF-radical seed that is linear over an m-adically separated ring is already linear over R/pR for a prime p dividing m, or its radical meets every congruence level
distinct_from:
  integral-group-ring-congruence-groups-are-torsion-free-mf: that proves the level-3 congruence groups over Z[G] are torsion-free with residually finite finitely generated subgroups; this generalizes the residual finiteness to every m-adically separated coefficient ring (Leavitt, Jacobson, free algebras, completions) and adds the reduction dichotomy for seeds that are linear but not inside a congruence kernel, which that node does not address.
  filtered-torsion-certificates-die-on-perfect-kernels: that kills maps of perfect kernels into filtered groups, so congruence groups cannot certify torsion-freeness of the quotientless kernel; this concerns an arbitrary linear seed, perfect or not, and shows the congruence kernel either meets the seed trivially (then the seed is characteristic-p linear) or meets its radical at every depth.
  torsion-free-seeds-need-kernel-descent-or-trace-corner: that is a countermodel obstruction for the abstract radical calculus; this is a concrete structural reduction for the linear-over-separated-ring class, whose surviving branch (B) is an instance of the kernel-descent gate named there.
  virtually-torsion-free-infinite-mf-radical-gives-seed: that is the finite-index-trace gate; part (0) here shows that no finitely generated group containing a congruence kernel over a separated ring with finite index can feed it, since such a group is residually finite.
artifacts:
  - research/separated-ring-linear-seeds-char-p-or-deep-radical-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`separated-ring-linear-seeds-char-p-or-deep-radical-proof`.

## Setting

- `R` is a unital ring, not necessarily commutative, and `m >= 2` is an
  integer with `intersection_j m^j R = 0`.  We say `R` is *m-adically
  separated*.  Examples:
  - any ring that is free as an abelian group, for every `m`: `Z`, `Z[G]`,
    the integral Leavitt algebra `L_Z(1,n)`, the integral Jacobson algebra
    `Z<s,t | ts = 1>`, and free algebras `Z<x_1,...,x_k>`;
  - `Z_p`, `Z_p[[t]]`, and their matrix rings, for `m = p`.
- `Gamma(q) = ker(GL_n(R) -> GL_n(R/qR))` is the level-`q` congruence
  subgroup, and `pi_q` is the reduction map.
- `r = rad(m)` is the product of the distinct primes dividing `m`.
  `R` is `r`-adically separated too, because `r | m | r^J` for some `J`.
- A group `E` is **(NC)** if `C_E(N) = 1` for every nontrivial normal
  subgroup `N`.  Every torsion-free acylindrically hyperbolic group is (NC).
  So every candidate for `(TFS1)` in `torsion-free-fp-ah-mf-radical-seed`
  is (NC).

## Theorem

**(0) Congruence kernels are locally residually finite.**  Every finitely
generated subgroup `H <= Gamma(m)` is residually finite, and so is MF.  Its
quotients `H / (H cap Gamma(m^j))` are finite nilpotent groups whose orders
involve only primes dividing `m`.  So every finitely generated `G <= GL_n(R)`
with `G cap Gamma(m)` of finite index in `G` is residually finite, and
`Rad_MF(G) = 1`.  Finiteness of `R/mR` is not needed for the first sentence.

**(1) Radicals descend to every reduction.**  For every `G <= GL_n(R)` and
every `1 != d in Rad_MF(G)`, there is `j_0` such that for all `j >= j_0`:

```text
1 != pi_(m^j)(d) in Rad_MF(pi_(m^j)(G)) <= GL_n(R/m^j R).
```

**(2) Seed dichotomy.**  Let `E <= GL_n(R)` be (NC) with `Rad_MF(E) != 1`,
and put `N_j = E cap Gamma(m^j)`.  Exactly one of the following holds:

- **(A) Characteristic-p linearity.**  `N_j = 1` for some `j`.  Then
  `E cap Gamma(p) = 1` for some prime `p | m`, so `E` embeds in
  `GL_n(R/pR)`, a group over an `F_p`-algebra.
- **(B) Deep radical.**  `Rad_MF(E) cap N_j != 1` for every `j`.  Then `E`
  has a decreasing chain of nontrivial normal subgroups
  `D_j = Rad_MF(E) cap Gamma(m^j)`, all inside the MF radical, with trivial
  intersection.  Every finitely generated subgroup of every `D_j` is
  residually finite.

In (B), `E cap Gamma(p) != 1` for every prime `p | m`.

**(3) Commutative coefficients die outright.**  Let `E` in (2) be finitely
generated.  If `R/pR` is commutative for every `p | m`, branch (A) is
impossible.  A finitely generated linear group
over a commutative ring is residually finite (Mal'cev), so it has trivial
MF radical.  If `R` itself is commutative, `E` is residually finite and no
branch survives.

## What this kills

The wave-22 suggestion was to use the level-4 congruence subgroups of
`GL_n(L_Z(1,2))` as torsion-free carriers for `(TFS1)`.  This whole class
dies, for every coefficient ring that is m-adically separated and every
level:

- **No seed inside a congruence kernel.**  A finitely presented `E <= Gamma(m)`
  is residually finite by (0), so `Rad_MF(E) = 1`.  This is the step where
  every member dies: the invariant is the m-adic congruence filtration
  `Gamma(m^a)`.  Its layers are abelian of exponent dividing `m` and
  commute into higher layers, so every finitely generated subgroup has
  finite image at each depth.  Whatever torsion-freeness a level
  condition provides comes from this same filtration, and the filtration
  also makes every finitely generated subgroup of the carrier MF.
- **No finite-index trace from a congruence kernel.**  If `E` is finitely
  generated and `E cap Gamma(m)` has finite index, then `E` is residually
  finite.  So the gate `virtually-torsion-free-infinite-mf-radical-gives-seed`
  can never be fed by a congruence subgroup over a separated ring.  Over
  Leavitt coefficients this trace is not even available, because
  `L_Z / m L_Z = L_(Z/m)` is infinite and the index is infinite.
- **Congruence buys nothing for linear seeds.**  If `E` is linear over `R`
  but not inside `Gamma(m)`, then by (2) either the congruence structure
  is invisible on `E`, or the radical sits in the congruence kernels:
  - in (A), `E cap Gamma(p) = 1` and `E` is linear in characteristic `p`,
    so the congruence filtration meets `E` trivially;
  - in (B), the radical meets every congruence level, which is a kernel-descent
    problem.

## Where the surviving routes sit

For the integral Leavitt algebra, `R/pR = L_(F_p)(1,2)` and
`M_n(L) ≅ L`.  So:

```text
(TFS1) seed linear over L_Z(1,2)
   ==>  (A) a torsion-free AH (TFS1)-seed inside the unit group L_(F_p)(1,2)^x,  some p | m,
    or  (B) Rad_MF(E) cap Gamma(m^j) != 1 for all j.
```

- **Branch (A)** puts the torsion-free leg of the flagship into the same
  characteristic-`p` unit groups as the Leavitt leg
  `property-t-free-leavitt-full-mf-radical`.  Those unit groups contain
  torsion, so torsion-freeness of `E` must now be proved directly, not by
  a congruence certificate.  Branch (A) is not vacuous.  Thompson's `V`, and so
  free groups and Thompson's `F`, embed in `L_(F_p)(1,2)^x` as the
  prefix-code permutation units.  `F` is torsion-free but not
  acylindrically hyperbolic.
- **Branch (B)** is the kernel-descent gate (item 4 of
  `torsion-free-seeds-need-kernel-descent-or-trace-corner`).  Some
  operator-norm property of `E` must kill a normal subgroup `D_1` that is
  locally residually finite.  This has the same shape as
  `full-mf-radical-abelianized-cover-is-not-mf`, where the kernel is abelian.
- **Commutative and Mal'cev-type coefficients** (`Z`, `Z_p`, `O_K`, and any
  commutative separated `R`) die outright by (3).

So among separated-ring constructions, only noncommutative
characteristic-`p` linearity (A) and deep radicals (B) remain.  Neither is
helped by a congruence level.

## How it fails

It does not fail; it is a theorem.  Each hypothesis is used at one step:

- **(NC) is used only in (2).**  It is what turns "the radical misses a
  congruence level" into "the level misses `E`".  Only this step needs it:
  two commuting nontrivial normal subgroups, a congruence kernel and a
  radical with trivial intersection.  Such a configuration is possible in
  direct products, which are never acylindrically hyperbolic.
- **Separation is used in (0) and (1).**  A non-separated ring, for example
  one with `R = mR` such as `R ⊗ Z[1/m]`, has `Gamma(m) = GL_n(R)` and no
  filtration.
