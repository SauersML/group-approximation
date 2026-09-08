---
rg: 2
id: binary-leavitt-hyperlinear-iff-24k-feasible
kind: claim
title: Hyperlinearity of the binary Leavitt unit group is one 24k-dimensional relative-unitary feasibility problem
distinct_from:
  leavitt-regular-atlas-hyperlinearity-criterion: that freezes two copies of A_8, works in dimension 20160k, and passes through the universal central extension with a fixed finite normal generating set; this freezes C_3 and C_2^3, works in dimension 24k, uses no central extension, and takes an explicitly enumerable relation family instead of asserting a finite one.
  binary-leavitt-hyperlinear-iff-singular-near: that characterizes hyperlinearity by proximity of a singular element to the invertibles; this characterizes it by vanishing of an explicit finite-dimensional unitary optimization with both finite factors frozen.
  binary-leavitt-units-generated-by-c3-and-c2-cubed: that is the group theory -- two finite abelian subgroups generate -- with no analysis; this is the analytic equivalence built on it, including the recovery of uniform separation.
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

**ESTABLISHED.**  Let `q : P = C_3 * C_2^3 -> H` be the surjection of
`binary-leavitt-units-generated-by-c3-and-c2-cubed`, `N = ker q`, and let
`r_*` be the fixed kernel word displayed in
`leavitt-24k-first-relation-has-exact-finite-model`. For `m>=1`, let
`T_m` consist of `r_*` together with every reduced free-product word of
length at most `m` for which each of the nine entries of its expanded
matrix minus `I` has an ideal certificate with at most `m` summands over
the five defining polynomials of `R`, each left and right factor being a
monomial of length at most `m`. Free-product length counts nonidentity
factor syllables. These are computable finite sets with
`T_1 subset T_2 subset ...` and union `N`; the artifact proves these facts.
The explicit word-length bound is essential: zero polynomial entries
alone impose no bound on the length of their group words. On

```text
Hilbert space  C^3 (x) C^8 (x) C^k,     dimension 24k,
C_k |a,b,j> = |a+1, b, j>,     D_(i,k) |a,b,j> = |a, b+e_i, j>,   (LK1)
```

so that `C_k` is the regular representation of `C_3` with multiplicity `8k`
and the `D_(i,k)` are the regular representation of `C_2^3` with multiplicity
`3k`, define for `U in U(24k)` the exact representation of `P`

```text
pi_(k,U)(c) = C_k,      pi_(k,U)(b_i) = U D_(i,k) U^*,            (LK2)
```

and put

```text
Delta_m = inf_(k>=1) min_(U in U(24k)) max_(r in T_m)
              || pi_(k,U)(r) - I ||_(2,24k).                      (LK3)
```

Then

```text
H is hyperlinear   <=>   Delta_m = 0 for every m.                 (LK4)
```

Equivalently, `H` fails to be hyperlinear if and only if some `T_m` carries a
lower bound `eta > 0` valid for **every** `k` and **every** `U in U(24k)`.

**The separation is proved, not assumed.**  In the direction from feasibility
to hyperlinearity the induced homomorphism into the tracial matrix
ultraproduct is nontrivial because `tr(C_k) = 0`, hence
`||C_k - I||_2 = sqrt 2`, and it is injective because `EL_3(R)` is simple
(`binary-leavitt-elementary-group-is-simple`).  Finite models with the single
separation constant `1` for every finite subset are then produced explicitly
by the amplification `V -> (I (+) V)^(tensor r)`.

Both finite factors are frozen in advance, so the only unknown is one
relative unitary.  Nothing here decides `(LK4)`; the two branches are
`leavitt-24k-feasibility-vanishes` and
`leavitt-24k-feasibility-has-a-uniform-gap`.
