---
rg: 2
id: perfect-completeness-isomorphism-compiler
kind: claim
title: A computable graph-pair family that is finite-dimensionally quantum isomorphic on halting machines and not quantum-approximately isomorphic on nonhalting machines
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
  - research/artifacts/ex-kac-quantum-compiler-torsor-profiles-2026-09-13.md
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that asks for linear constraint systems, whose gap is goal-equivalent; this asks for graph pairs, whose quantum symmetry need not be a group dual.
  qc-isomorphic-not-qa-isomorphic-graph-pair-exists: that asks for one pair; this asks for a machine-indexed family with finite-dimensional completeness, which the constant compiler built from one pair cannot supply.
  bisynchronous-to-monomial-game-algebra-compiler: that asks for an exact encoding of one fixed non-CE game algebra; this asks for a total computable family with an RE-hardness orientation.
---

**OPEN.**  Construct a total computable map `M |-> (X_M, Y_M)` from Turing
machines to pairs of finite simple graphs such that

```text
M halts          =>  X_M ≅_q Y_M   (a nonzero finite-dimensional representation
                                     of A(Iso(X_M,Y_M))),               (IC1)
M does not halt  =>  X_M not ≅_qa Y_M.                                  (IC2)
```

`qc-qa-graph-gap-from-perfect-completeness-iso-compiler` turns such a map
into a pair for `qc-isomorphic-not-qa-isomorphic-graph-pair-exists`, and hence
into a finite graph with non-Connes-embeddable quantum automorphism group.
It would also make `qa`-isomorphism RE-hard.

**Weak form versus strong form.**
- **Weak form.**  Replace (IC1) by `M halts => X_M ≅_qc Y_M`.  The fixed-point
  argument still works.
  - This form is equivalent to the existence of one pair: the constant map
    `M |-> (X_*, Y_*)` satisfies it.
  - So the weak form is a reformulation, as in
    `lcs-compiler-target-is-goal-equivalent`.
- **Strong form.**  (IC1) asks for finite-dimensional isomorphisms on
  halting inputs.
  - The constant map fails: `X_* ≅_q Y_*` would give `X_* ≅_qa Y_*`.
  - Any strong compiler is therefore a genuine reduction.  This is the
    orientation in which the `MIP*=RE` completeness strategies are
    finite-dimensional.

## Attempts

- **Linear-system compilers.**  Composing a perfect-completeness LCS compiler
  with the CFI bridge works.
  - It is goal-equivalent: `lcs-compiler-target-is-goal-equivalent` and
    `qc-qa-graph-gap-from-perfect-completeness-lcs-compiler`.
  - Its quantum symmetry is a group dual
    (`colored-cfi-rung-is-the-solution-group-case`).
- **Unchanged `MIP*=RE` verifiers, compiled context by context.**  The active
  compression output has no affine-safe perfect model
  (`jnvwy-active-output-has-no-affine-safe-perfect-model`).  Where it dies:
  - every direct Harris-circulant colour encoding sees only affine support
    (`harris-circulant-one-matrix-compiler-forces-affine-support`);
  - one-matrix monomial encodings see only projective colour classes
    (`monomial-game-pair-compatibility-is-projective-color-rigid`).
- **Nonabelian local symmetry of torsor type.**  CFI over any finite group `H`
  gives isomorphism algebras that are `H`-valued coset constraint algebras
  (`torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra`), with
  non-group-dual quantum symmetry.  Where it dies:
  - scalar port profiles are cosets, and affine on Boolean ports, at the `q`,
    `qa` and `qc` levels (`torsor-cfi-port-profiles-are-cosets`);
  - so atom-by-atom torsor gadgets cannot realize NAND.
- **Uniform classical-solution-preserving gadgets.**  Blocked by the Babai
  argument recorded on `qc-isomorphic-not-qa-isomorphic-graph-pair-exists`
  (conditional on NP not in quasipolynomial time).
- **What is not excluded.**
  - Gadget families whose port variations are not twists of one graph.  The
    quantum isomorphism groupoid survives, but the twist identity, the only
    torsor input to the coset theorem, does not.
  - Ports coupled non-scalarly to the instance.
  - Compilers that change the recursive sampler or proof interface of the
    verifier, so that the honest halting strategy is symmetric: its trace is
    the invariant trace of a bigalois extension.
