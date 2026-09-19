---
rg: 2
id: leavitt-cone-head-bound-holds-for-all-ring-shadows
kind: claim
title: The cone-cover head bound (QC) holds with a uniform linear constant for every ring-induced representation of the Cuntz-cone cover, over any ring, radical included
distinct_from:
  leavitt-cone-head-bound-holds-for-semisimple-ring-shadows: that proves (RS) only when the shadow ring is finite semisimple and names radical shadows as a survivor; this proves (RS) for every shadow ring (finite or infinite, any radical), i.e. for every representation factoring through St_20 of the amalgamated ring R_+ *_(R_0) R_-, so radical shadows are dead and only non-ring gluings survive.
  leavitt-cone-cover-hamming-head-bound-holds: that proves (QC) on permutation and finite-phase monomial representations via nonsoficity of R^x; this proves it on the ring-induced class, which contains arbitrary non-monomial unitary representations of St_20(B), with a direct character argument.
  leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding: that splits non-hyperlinearity of Delta into (QC) and (HR) and leaves (QC) open; this proves (QC) on one explicit class and identifies the relators whose approximate triviality is all that remains.
  char-two-root-displacement-is-two-sided-ideal-dominated: that is the general ring-free comparison lemma; this is its application to the Leavitt defects of the cone cover.
artifacts:
  - research/leavitt-cone-head-bound-all-ring-shadows-proof.md
  - research/char-two-root-displacement-ideal-domination-proof.md
  - experiments/ring-shadow-head-bound-2026-09-17/verify_block_averaging.py
---

**ESTABLISHED** (route `leavitt-cone-head-bound-all-ring-shadows-proof`; lane swarm-0917-w17-w17-ptl-pull,
transplanter/reframing; unreviewed).

**Setting** (`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`,
`leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`).
- `R = L_(F_2)(1,2)`, `q = s_1 t_1`, `R_+ = <s_1, s_2, q>`, `R_- = <t_1, t_2, q>`, `R_0 = F_2 1 + F_2 q`.
- `Gamma = Delta_+ *_(Delta_0) Delta_-` with `Delta_+- = St_20(R_+-)` and `Delta_0 = St_20(R_0)`; `K` is the normal
  closure of `k_1, ..., k_r`; the head is `z = x_13(q)`; norms are normalized Hilbert--Schmidt.
- `P = R_+ *_(R_0) R_-`, the amalgamated free product of unital `F_2`-algebras. The inclusions
  `R_+- -> P` induce `Phi_P : Gamma -> St_20(P)`.

**Ring-induced representations.** A finite-dimensional unitary representation `rho` of `Gamma` is *ring-induced* if
`rho = pi o St_20(phi) o Phi_P` for a unital ring map `phi : P -> B` and a unitary representation `pi` of
`St_20(B)`. Equivalently, `rho` factors through `Phi_P`. Pairs of ring maps `R_+- -> B` agreeing on `R_0` are the
same thing as maps `P -> B`, so this is exactly the "one-ring shadow" class, with `B` arbitrary (finite or not,
semisimple or not).

**Theorem.** With `L_d` the fixed word lengths of the six Leavitt defect commutators `g_d` in the `k_i^(+-1)`
(`leavitt-cone-head-bound-semisimple-ring-shadows-proof`, Step 1), every ring-induced `rho` satisfies

```text
||rho(z) - 1||_2  <=  sqrt(30) * max_d L_d * max_i ||rho(k_i) - 1||_2.                    (RS_all)
```

The constant does not depend on `B`, `phi`, `pi` or the dimension.

**Proof idea.**
1. `Phi(g_d) = x_13(d)` for the six defects `d` of `(D6)`, and these generate `B` as a two-sided ideal. Both facts
   are Steps 1--2 of the semisimple route, valid for every finite `B`. Infinite `B` is reduced to a finite quotient
   by `positive-characteristic-steinberg-unitary-images-are-finite`.
2. `char-two-root-displacement-is-two-sided-ideal-dominated` with `n = 20`, `p = r = 10`, `(i0, j0) = (1, 3)`,
   `e_i` the six defects and `Q = phi(q)`, gives `||rho(z) - 1||_2^2 <= 5 sum_d ||rho(g_d) - 1||_2^2`.

## What this settles and kills

- **Class killed: every ring-induced refutation of `(QC)`.** A failure of `(QC)` would make `Delta` hyperlinear
  and refute `(LNC3)` (`leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`). The next step named in
  `leavitt-cone-head-bound-is-finite-congruence-gluing`'s lane asked for "a uniform bound [that] would prove `(QC)`
  for all ring-induced gluings". This is that bound.
  - *Invariant:* the largest two-sided ideal `J(c)` on which a character `c` of the two-sided block root group
    `M_(10 x 10)(B)` vanishes.
  - *Death step:* `1[q not in J(c)] <= sum_d 1[d not in J(c)]`, because the defects generate `B`. It is read
    through a two-sided averaging that makes displacement equivalent, up to the factor 5, to
    `mu{c : e not in J(c)}`.
  - The "radical shadows" survivor of `leavitt-cone-head-bound-holds-for-semisimple-ring-shadows` is dead.
- **What survives, exactly.** A counterexample to `(QC)` must be a genuine representation of `Gamma` that does
  not factor through `Phi_P : Gamma -> St_20(P)`, and must stay quantitatively far from doing so. In such a
  representation, the relators of `ker Phi_P` (cross-commutation `[x_ij(a), x_kl(b)]`, `a in R_+`, `b in R_-`,
  disjoint index pairs, and the consistency of products `x_ik(ab)` built through different middle indices) are only
  `delta`-trivial. So `(QC)` is now equivalent to its restriction to non-ring gluings, and on that class it is a
  stability statement for `ker Phi_P` inside `K`, not a ring or character statement.
- **Relation to the calibration.** By `leavitt-cone-cover-hamming-head-bound-holds`, a refutation of `(QC)` yields
  a hyperlinear nonsofic group. Together with this node, such a refutation must be non-monomial and non-ring-induced.
- **Status of the hole.** `agent-leavitt-not-bcs-negative-root-corner` stays OPEN. This is a class kill on the
  refutation side of `(QC)`, not a proof of `(QC)`.

## Attempts

Established; the proof is `leavitt-cone-head-bound-all-ring-shadows-proof`.
