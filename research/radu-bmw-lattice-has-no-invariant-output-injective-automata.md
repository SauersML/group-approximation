---
rg: 2
id: radu-bmw-lattice-has-no-invariant-output-injective-automata
kind: claim
title: Radu's BMW lattice carries no injective automaton whose output is invariant under a nontrivial subgroup
distinct_from:
  invariant-output-injective-ca-need-torsion: that forces the symmetry to be finite, so it says nothing on a host with torsion; this host has 2-torsion, and the symmetry still dies because every involution survives in a finite abelian quotient.
  invariant-output-injective-automata-need-invisible-symmetry: that places a finite symmetry in the sofic radical of the memory group; this proves the finite-quotient version on the host itself and applies it to one explicit lattice where every finite subgroup is visible in the abelianization.
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
---

**ESTABLISHED** by `radu-bmw-no-invariant-output-automata-proof`.

Let `Gamma_R` be Radu's BMW lattice (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`), `A` a finite
alphabet with `|A| >= 2`, and `H <= Gamma_R`. If `tau` is an injective cellular automaton on
`A^(Gamma_R)` with

```text
tau(x)(g h) = tau(x)(g)       for all x, all g, and all h in H,
```

then `H = 1`.

**Ingredients.**
- **Any group.** If an injective automaton on `A^G` has output invariant under `H`, then `H` lies in
  every normal subgroup `N` of finite index. The configurations constant on the cosets of `N` form a
  finite `tau`-invariant set of size `|A|^([G:N])`. Their outputs are constant on the cosets of
  `HN`, so injectivity forces `HN = N`.
- **This host.** By the fixed-cell classification on the product of trees, every involution of
  `Gamma_R` is conjugate to a letter or to `ax`, `ay` or `bx`. Each of these maps to a nonzero vector
  of `Gamma_R^ab = (Z/2)^3`. So no nontrivial finite subgroup lies in the index-eight subgroup
  `[Gamma_R, Gamma_R]`, while `invariant-output-injective-ca-need-torsion` makes `H` finite.

**Consequences.**
- The invariant-output family has no instance on `Gamma_R`, although `Gamma_R` has 2-torsion. That
  covers swap and Klein corner automata, and every design whose output is constant on cosets of a
  subgroup.
- For odd `p`, each involution `t` has a character with `chi(t) = -1`. It kills the averaging
  idempotent `(1+t)/2` of `F_p[Gamma_R]` at every matrix size: the low-degree case, through
  `low-degree-invariant-output-reduces-to-corner-fullness`.

Proof: Section 1 of the artifact.
