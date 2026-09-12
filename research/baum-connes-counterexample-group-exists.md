---
rg: 2
id: baum-connes-counterexample-group-exists
kind: claim
title: Some countable group violates the Baum--Connes conjecture with trivial coefficients
root: true
distinct_from:
  hyperbolic-bcc-finite-wreath-products: that is an established positive theorem, Baum--Connes with coefficients for hyperbolic groups after finite wreath products; this asks for a group whose reduced assembly map with trivial coefficients is not an isomorphism.
---

**OPEN.** There is a countable discrete group `G` for which the reduced
assembly map

```text
mu_r : K^G_*(Ebar G) -> K_*(C*_r G)
```

is not an isomorphism.

*Marked `root` because it answers a top-level question in its own right.*
Nobody knows a counterexample to the Baum--Connes conjecture with trivial
coefficients. Literature context, not imported here:
- it holds for groups with the Haagerup property (Higson--Kasparov) and for
  hyperbolic groups (Mineyev--Yu, Lafforgue);
- the version with coefficients fails for Gromov monster groups containing
  expanders (Higson--Lafforgue--Skandalis, GAFA 2002);
- it is open for `SL_3(Z)`.

**Test hosts in this graph.**
- The binary Leavitt unit group `L^x = L_(F_2)(1,2)^x`: finitely presented,
  simple, nonsofic, with property (T) through
  `binary-leavitt-unit-group-has-tt-mod-t`, and containing every finite group.
- The residually finite Kazhdan groups of the Kun--Thom Theorem E pairs.

Property (T) closes the Higson--Kasparov route for both.

## Attempts

- **Kazhdan projections.** Route `bc-counterexample-via-kazhdan-projection`.
  - Dead: the projection of an infinite Kazhdan subgroup maps to zero in
    `C*_r G`. Its class lies in `ker lambda_*` and says nothing about `mu_r`,
    only about the maximal assembly map.
  - Invalidated by `subgroup-average-projections-give-no-reduced-bc-obstruction`.
- **Leavitt compression classes.** Route
  `bc-counterexample-via-leavitt-compression-classes`.
  - Dead: Leavitt ring idempotents are not elements of `C[L^x]`. Subgroup
    averages are assembly images or zero, and the faithful trace of `C*_r G`
    collapses compression relations.
  - Same invalidator.
- **Rational trace mismatch on `L^x`.** Route
  `bc-counterexample-via-rational-trace-mismatch`.
  - Dead: every finite group embeds in `L^x`, so the finite-subgroup ring
    `Lambda^(L^x)` is `Q` (`leavitt-unit-group-contains-every-finite-group`).
  - Lück's theorem (Invent. Math. 149 (2002)) confines assembly traces only to
    that ring.
- **What survives, with no mechanism yet.**
  - A projection in some `M_n(C*_r L^x)` with irrational trace. Through
    Lück's theorem this refutes surjectivity of `mu_r`. It is a spectral
    question of Atiyah and Kadison--Kaplansky type: an isolated point of the
    spectrum of a self-adjoint element of `Q[L^x]` with irrational
    L^2-multiplicity.
  - An independent computation of `K_*(C*_r L^x)`. Rationally the left-hand
    side is the Baum--Connes Chern character sum, over conjugacy classes of
    finite-order elements `g`, of `H_*(C_G(g); C)`. Khanh's acyclicity of
    `L^x` controls only the `g = 1` summand. The centralizers of torsion
    elements are not controlled, and nothing in the graph computes the
    right-hand side.
  - **On the Kun--Thom actors the trace test is live.**
    `kun-thom-actor-finite-subgroup-ring-has-finitely-many-primes` confines
    `Lambda^G` to finitely many inverted primes `P(q,r,d)`. So a projection in
    `M_n(C*_r G)` with a rational trace outside `Z[1/l : l in P(q,r,d)]`
    would already refute surjectivity of `mu_r` for a Theorem E actor. On
    `L^x` no rational target exists. The difficulty is unchanged: no mechanism
    produces a projection in `C*_r G` that is not built from subgroup averages.
- **Algebraic idempotents on the Kun--Thom actors.**
  - Dead. `kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p` makes the
    target exactly `Lambda^G = Z[1/P(q,r,d)]`.
  - `kun-thom-actor-algebraic-idempotents-pass-trace-test` puts the trace of
    every idempotent of `M_n(C[G])` inside it.
  - Why: push the idempotent to congruence quotients chosen by Dirichlet, so
    that the index avoids any given prime outside `P`.
  - Every spectral projection of a finite-spectrum element is such an
    idempotent.
- **Markov operators on coset spaces over Kazhdan subgroups.** Not candidates.
  - `lambda_(G/H)` is weakly contained in `lambda_G` only when `H` is amenable.
    The Theorem E subgroup and `SL_d(Z)` are infinite Kazhdan groups.
  - So their coset-space spectral projections are not elements of `C*_r G`.
  - See the artifact `research/artifacts/bc-kun-thom-trace-test-2026-09-12.md`,
    Section 3.
- **What survives on the Kun--Thom actors, with no mechanism yet.**
  - A non-algebraic gapped spectral projection of a self-adjoint
    `a ∈ M_n(C[G])` with infinite spectrum. For integral coefficients its
    spectrum has capacity at least 1 (`integral-spectra-of-small-capacity-are-finite`).
  - Its trace is the limit, over large primes `p'`, of the eigenvalue fractions
    of `a` in the congruence quotients `G/N_(p')` below the gap
    (`bc-kun-thom-gap-label-is-congruence-eigenvalue-limit`, established).
    That claim is a reduction only. The artifact's Section 4 display carries an
    extra factor `1/n`.
  - A refutation needs this limit to leave `Z[1/P]`. Nothing in the graph
    controls such limits.
- **Supports inside a-T-menable subgroups.** Dead.
  - `bc-kun-thom-gap-labels-on-bc-subgroups-pass-trace-test` (established;
    imports Lück--Reich arXiv:math/0402405, Theorems 3.22 and 5.1, quoted from
    the extracted text). If `a` is supported on a subgroup `H` with surjective
    assembly, the gapped projection's trace lies in `Lambda^H`, inside `Z[1/P]`.
  - This rules out Borel, unipotent and lamplighter supports, corner blocks
    `E_2(F_q[x_1^(+-1)])` (which act properly on products of trees),
    `SL_2(Z)`, and finite products of these. These are exactly the test
    operators that can actually be computed.
  - So a refuting `a` needs support generating a subgroup that lies in no
    subgroup with surjective assembly, for example one containing `SL_3(Z)`.
- **Congruence numerics.** Infeasible. For `(q,r,d) = (2,3,3)` and `p' = 3`
  the quotient index is `168 · 60480^13 · 5616`, about `10^68`. See
  `research/artifacts/bc-gap-label-subgroup-support-2026-09-12.md`, Section 4.
- **Extension permanence is no shortcut.** Meyer, arXiv:2508.05726 (abstract
  read, not imported), shows that the Chabert--Echterhoff hypotheses cannot be
  weakened to Baum--Connes for the normal subgroup alone.
