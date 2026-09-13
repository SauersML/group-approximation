# Lane solve-bh-apapa, 2026-09-13: lamp wreaths and the KMS configuration module

Target: `fp-rf-apapa-groups-satisfy-boone-higman` (OPEN). It feeds the root
`fp-simple-groups-with-arbitrarily-complex-word-problem` through
`complex-fp-simple-groups-from-apapa-rf-boone-higman`.

## Outcome

- **Not solved.** The target stays OPEN.
- **Landed, positive:** `bh-type-a-class-closed-under-permutational-lamp-wreaths`.
  Finite lamps over a type (A) actor give a type (A) actor (Cornulier's wreath
  criterion plus a clause check). So `B wr_S Gamma`, and every subgroup of it,
  satisfies Boone--Higman.
- **Landed, obstruction:**
  - `invertible-difference-modules-are-not-permutation-submodules`, elementary
    linear algebra;
  - `kms-configuration-modules-avoid-abelian-lamp-bases`: in every embedding of a
    KMS group `G(MM_k)` into a permutational wreath product with abelian lamps,
    the configuration generators `x(q_j)` leave the base.
- **Consequence:** the placement "metabelian quotient `M` in a type (A) actor,
  configuration module `T` in finite abelian lamps" cannot give Boone--Higman for
  the hard groups in `A_p^2 A`.

## Sources read

- **Cornulier, arXiv:math/0509090,** TeX lines 147--157 on MSI
  (`/scratch.global/sauer354/bh-isolated/math_0509090.tex`), verbatim in
  `bh-type-a-lamp-wreath-closure-proof`.
- **Kharlampovich--Myasnikov--Sapir, Bull. Math. Sci. 7 (2017) 309--352,** PDF text
  (lane scratch `bhwp/kms-bms.txt`):
  - §4.1, pp. 333--335: generators `L_0, L_1, L_2`, relations (G1)--(G8), Lemma 4.1,
    Remark 4.2;
  - Theorem 4.3, pp. 335--336;
  - Lemmas 4.4, 4.5, p. 336;
  - the automorphisms of `T_1`, pp. 338--340;
  - Lemmas 4.9--4.15 and Theorem 4.18, pp. 340--344.

## Structure of the hard module (from the source)

- **Normal form.** `T` has basis `x(i, w)`, where `i` runs over `{1,2,3}^k` and
  `w` over the nonzero words of `Š` or their images in `S(MM_k)` (Lemma 4.13).
- **The `a`-letters are not monomial.** For `w` without `A_j` and `i_j = 1`,
  `z(i,w)^(a_j) = z(i,w) z(i+e_j,w) z(i+2e_j,w) z(i, w a_j)` (p. 339). So `T` is
  not a permutation module for `<a_j>`.
- **The conjoint is a difference operator.** On the submodule of words without
  `A_j`, `a'_j` acts as `a_j - 1` (Remark 4.2). So `a_j - 1` is invertible there,
  and the derived operation `∗ a_j` acts as `(a_j - 1)^(-1)`, consistent with
  Lemma 4.9.
- **Where the obstruction comes from.** A permutation module cannot hold an
  infinite `a_j`-orbit on which `a_j - 1` is invertible: the (t-1)-adic valuation
  of Laurent polynomials is bounded.

## Attempts in this lane

1. **Lamp placement with abelian lamps.** Dead, by
   `kms-configuration-modules-avoid-abelian-lamp-bases`.
2. **Affine actor `T x| M` acting on `T`.** It is faithful, finitely presented,
   and its point stabilizers are conjugates of `M`, hence finitely generated. It
   is of type (A) exactly when `M` has finitely many orbits on `T \ {0}`. Not
   decided here. Unlikely, since `M` is metabelian and `T` is infinite-dimensional
   with orbits of unbounded support, but no proof was written.
3. **Zero tests via singular germs** (the SingFix shape from the bh-fp-criterion
   ideas file). Not attempted. The zero tests of the machine are the relations
   `x(q_i A_0) ∗ A_(n_1) ∗ ...` in (G8), which act through the `A`-letters. The
   difference-operator structure of Step 1 of `kms-lamp-base-obstruction-proof`
   applies only to the `a`-letters.

## Exact remaining gap

A type (A) actor containing some `G(MM_k)` for each recursive time bound, in which
the configuration letters act outside abelian lamps. The untested placements are
nonabelian finite lamps, top-group placement and germ placement.
