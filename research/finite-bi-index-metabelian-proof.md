---
rg: 2
id: finite-bi-index-metabelian-proof
kind: route
title: Pass to the abelian orbit module, count content for lattices and units for fields
target: finite-bi-index-forces-finite-index-in-metabelian-groups
requires: []
artifacts:
  - research/artifacts/commuting-conjugate-coset-switch-2026-09-16.md
---

## Why sufficient

This is the full argument of Section 4 of the artifact (Lemmas 6.1--6.5,
Theorem 6, Corollary 7), condensed. The theorem is a special case of Cornulier,
arXiv:math/0509090v2, Proposition 3.20 with Lemma 3.2, which relies on
Roseblade's theorem. The argument below is independent of that source and uses
no imported theorem. Throughout, `Y` is a transitive `K`-set of finite rank.

**L1 (finite index).** Let `L <= K` have index `m`. Then `K.p` is the union of
the `L.(g_j p)` over coset representatives `g_j`. Applying this to `Y` and to
`Y x Y` shows:

- `Y` has at most `m` orbits of `L`;
- each `L`-orbit on `Y x Y` lies inside one `K`-orbit, and each `K`-orbit splits
  into at most `m` of them.

So each `L`-orbit of `Y` is a transitive `L`-set of finite rank.

**L2 (quotients).** For `N <| K`, the set `Y/N` is a transitive `K/N`-set. The
surjection `Y x Y -> Y/N x Y/N` is equivariant, so `Y/N` has finite rank.

**L3 (orbit module).** Let `A <| K` be abelian, fix `y in Y`, and put
`A_y = A cap K_y`, `S = A K_y`, `R = S/A` and `M = A/A_y`.

- The `A`-orbits are blocks permuted transitively by `K`. Also `s(A.y) = A.y` iff
  `a^-1 s in K_y` for some `a in A`. So `S` is the setwise stabilizer of `A.y`, and
  `|K : S| = |Y/A|`.
- `K_y` acts on `M` by conjugation, with `A_y` acting trivially, so `R` acts by
  automorphisms.
- `a A_y -> a.y` is an `R`-equivariant bijection `M -> A.y`.
- `(y, a.y)` and `(y, a'.y)` share a `K`-orbit iff `a'.y in K_y.(a.y)`. So `R` has
  at most rank-many orbits on `M`.
- For `g in K`, `A_(gy) = g A_y g^-1`, so every `A`-orbit has `|M|` points.
- Hence `|Y| = |Y/A| . |M|`.

**L4 (lattices).** Let `M` be finitely generated abelian with `M/T = Z^s`, `s >= 1`,
where `T` is the torsion subgroup. The largest `n` with `vbar in n(M/T)` is
invariant under automorphisms. It takes the value `n` on `n w`, where `w` maps to
a basis vector. So there are infinitely many orbits under any automorphism
group.

**(i).** By L1 we may take `K = L` polycyclic. Subgroups of polycyclic groups
are finitely generated: intersect the series, and each factor embeds in a
cyclic group. Quotients of polycyclic groups are polycyclic. Induct on the derived
length `d`; `d = 0` is trivial. Otherwise:

- `A = L^(d-1)` is abelian, normal and finitely generated.
- `Y/A` is finite by L2 and induction, since `L/A` has derived length `d - 1`.
- `M = A/A_y` is finitely generated with finitely many orbits under
  automorphisms. By L4 it has rank `0`, so it is finite.
- By L3, `Y` is finite.

**(ii).** `K/A` is finitely generated and virtually abelian, so it is virtually
polycyclic. So `Y/A` is finite by L2 and (i). Then:

1. `S` has finite index in `K`, so it is finitely generated. `R <= K/A` is finitely
   generated and virtually abelian. Pick an abelian `R_0 <= R` of finite index.
   By L3 and L1, `R_0` has finitely many orbits on `M`.
2. Since `r in R_0` is a unit of `Z[R_0]`, `Z[R_0](rm) = Z[R_0]m`. So there are
   finitely many cyclic submodules. Every submodule is a union of cyclic ones, so
   there are finitely many submodules. So `M` has a composition series
   `0 = M_0 < ... < M_t = M`.
3. `M_i` is a union of `R_0`-orbits of `M`, and the map `M_i -> M_i/M_(i-1)` is
   equivariant and onto. So every simple factor `V` has finitely many orbits.
4. `V = Z[R_0]v = Z[R_0]/Ann(v)`, and simplicity makes `Ann(v)` maximal. So `V` is a
   field `F` on which `r` acts by multiplication by `rbar`. The orbits of the
   finitely generated group `Gamma = {rbar}` on `F^x` are the cosets. Finitely
   many cosets means `F^x` is finitely generated.
5. **Fields lemma.** Suppose `F^x` is finitely generated. Then all its subgroups are
   finitely generated, so no free abelian subgroup has infinite rank.
   - `char F = 0` is impossible: the primes are multiplicatively independent in
     `Q^x`.
   - A transcendental `t` over `F_p` is impossible: by Euclid's argument there are
     infinitely many monic irreducibles in `F_p[t]`, and their values at `t` are
     independent by unique factorization.
   - So every `x != 0` is algebraic over `F_p`. Then `F_p[x]` is finite, so `x` has
     finite order. `F^x` is therefore a finitely generated torsion abelian group,
     hence finite, and so `F` is finite.
6. All composition factors of `M` are finite, so `M` is finite, and L3 gives `|Y|` finite.

**Finite bi-index.** `K/C` has rank `|C\K/C|`. So finite bi-index gives finite
index.

**Consequence.** Soundness of the certificate: the base point is fixed by
`S_(C_e)`, and the Schreier generators of `Stab(y_0)` are derived to lie in
`C_e`. So `Stab(y_0) = C_e`, and `Y = K_e/C_e` equivariantly. The orbit cover then
says exactly `K_e = D_e`.

Completeness: `K_e = D_e` gives `|C_e\K_e/C_e| <= 1 + 2|U_e|`. By the theorem the
coset action is finite. With `y_0 = C_e` it is transitive, satisfies the
relators, has `y_0` fixed by `S_(C_e)`, and has its point set covered by the
three listed kinds of `C_e`-orbits. Since `Stab(y_0) = C_e`, every Schreier
generator lies in `C_e`, so the required derivations exist. So the coset action
is a certificate. Certificates are
finite and can be enumerated and checked, so the locus is `Sigma^0_1`. `QED`
