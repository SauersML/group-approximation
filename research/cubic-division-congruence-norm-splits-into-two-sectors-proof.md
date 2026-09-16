---
rg: 2
id: cubic-division-congruence-norm-splits-into-two-sectors-proof
kind: route
title: Mackey kills generic functionals on vectors, a class count forces exhaustion for GL_3, Clifford restriction descends to SL_3, and the Gelfand--Graev character is a Borel computation
target: cubic-division-congruence-norm-splits-into-two-sectors
requires: [cubic-division-ihara-traces-count-roots-mod-p, free-group-ihara-bass-outlier-trace-criterion]
artifacts:
  - research/artifacts/cubic-division-congruence-norm-splits-2026-09-16.md
---

Full details are in the artifact.  Throughout, `G~ = GL_3(F_p)`, and "generic" means "a constituent of
`Ind_U psi_(1,1)`".

1. **No generic vectors** (artifact, Lemma 1).  By Mackey, a `psi_a`-intertwiner into `Ind_Q 1`, with
   `Q = Stab(e_1)`, lives on the double cosets `U g Q`.  On each of them, `U cap Stab(g e_1)` contains a
   root subgroup on which `psi_a` is nontrivial.
2. **Vector-type irreducibles of `GL_3`** (Section 2A).  The det-twists of `l^2(F^3 minus 0)` are the
   `Ind_(P_(1,2))(chi (x) mu o det)`.  Mackey over the two double cosets of `P_(1,2)` shows that they
   contain exactly `p(p-1)` distinct irreducibles, none generic.
3. **Generic count** (Section 2B).  Bruhat and Mackey give
   `dim End(Ind_U^(G~) psi) = (p-1) + 2(p-1)^2 + (p-1)^3 = p^3 - p^2`.  With multiplicity one (import), there
   are `p^3 - p^2` generic irreducibles.
4. **Exhaustion for `GL_3`** (Section 2C).  `GL_3(F_p)` has `p^3 - p` classes (rational canonical forms),
   and `p(p-1) + (p^3 - p^2) = p^3 - p`.
5. **Descent to `SL_3`** (Section 2D).  Every irreducible of `G` lies in the restriction of an irreducible
   of `G~`.  The restriction of the vector sector is `sigma_p`.  By Mackey and torus conjugation, the
   restriction of `Ind_U^(G~) psi` is a sum of the `Ind_U^G psi_a`, and these depend only on `a` mod cubes.
   Part 1 of the claim follows, since norms are maxima over constituents (Theorem 4).
6. **Equivalence** (Corollary 5).
   - The vector-sector characters of a fixed `w != 1` equal `-1` once `p` does not divide `Delta(w)`.
   - The Gelfand--Graev characters vanish off unipotents.  `w mod p` is unipotent only if
     `f_w == (x-1)^3 mod p`.  Since `f_w` is irreducible over `Q` (both from
     `cubic-division-ihara-traces-count-roots-mod-p`, part 1 and the reduction paragraph), this fails for
     large `p`.
   - Convergence in distribution then gives the lower bounds, and Theorem 4 the upper bound.
7. **Character** (Proposition 6).
   - At `1` the value is the index `|G/U|`.
   - At transvections: a single class, centraliser order `p^3 (p-1)`, and a character sum over the rank-1
     elements of `U` equal to `-(p+1)`.
   - At regular unipotents: a unique Borel, a torus sum, and a sum over `a` that turns the torus sum into
     a product of two complete Gauss-type sums, each `-1`.
   - Checks: orthogonality to constants, and exact evaluation at `p = 5, 7, 11, 13` (Section 6).
8. **Traces** (Proposition 7).  Evaluate 7 at `w mod p`.  Part 4(a)(b) of the claim is 4(a)(b) of
   `free-group-ihara-bass-outlier-trace-criterion` with `k = 2`, `d = d_p`.  Here `p <= d_p <= 3 p^5`, so
   `n_p / log p -> infinity` iff `n_p / log d_p -> infinity`.
