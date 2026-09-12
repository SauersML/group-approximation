# Sofic charts force a global character-energy floor

Date: 2026-08-30

Status: proved by the explicit finite Fourier carrier below.

## Result

For a sofic action on a binary permutation module with a nonzero seed whose
visible character orbits have one uniform Schreier gap, every finite word
window has finite models with:

- an exact representation of the whole module;
- vanishing defect on every relation in the chosen window;
- seed-negative spectral mass tending to `1/2`; and
- complete actor transport energy at least `gamma-o(1)`.

Thus local action charts do not merely fail to prove global transport: they
give quantitative adversaries to every seed-preserving decoder.

## Construction

For a finite chart carrier `D`, label set `N`, and chart labels `ell_x(d)`,
use the Hilbert space

```text
ell^2(D x F_2^N).
```

The whole module acts diagonally through the finite linear maps

```text
j_d(m)=sum_x m_x delta_(ell_x(d)).
```

This is an exact module representation even on collision carriers.  Actor
generators permute only `D`.  Chart equivariance makes every prescribed
fixed covariance law exact off `o(|D|)` carriers.

Injectivity on the finite support of the nonzero seed makes `j_d(m_0)`
nonzero on `1-o(1)` of `D`.  Fourier balance on `F_2^N` then gives exactly
one-half negative seed spectrum on every such carrier.

## Energy calculation

Close the finitely many occurring seed-negative characters under `A`.
Every resulting orbit has bottom gap at least `gamma`.  The established
finite-support Schreier-PVM inequality gives

```text
E >= 2 gamma mu_negative >= gamma-o(1).
```

The whole-module averaging identity converts this into a virtual module word
whose covariance defect stays at least `sqrt(gamma)-o(1)`.  That word moves
with the chart stage, explaining why every fixed word test still succeeds.

If a decoder replaces the exact chart module by another exact
representation close on the seed, the normalized trace identity

```text
tr(1_(-1)(rho(m_0)))=(1-tr(rho(m_0)))/2
```

preserves the half-mass up to half the normalized-HS seed error.  The same
gap therefore forces the same energy floor for the decoder output.

## Pauli consequence

The common-center Pauli chart is a noncommutative enlargement of this exact
first-coordinate construction.  Its diagonal central sign and second Pauli
coordinate do not change the Fourier mass or its character-energy floor.
Accordingly, bare Pauli relations over a sofic action cannot close the
infinite-character interface.

## Scope

This is not a refutation of the existential Cairn target.  It establishes
the exact surviving dichotomy:

```text
successful interface
  => nonsofic underlying action
     or a controller relation destroyed by the Pauli chart quotient.
```

For the dyadic `SL_3` host, action soficity is presently open, so the result
turns word-energy soundness into a genuine nonsoficity-strength obligation.
For the sharply two-transitive host, neither actor nor action soficity is
known.  No unconditional `invalidates:` edge to those existential routes is
justified.