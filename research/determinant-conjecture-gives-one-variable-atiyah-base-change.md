---
rg: 2
id: determinant-conjecture-gives-one-variable-atiyah-base-change
kind: claim
title: Under the determinant conjecture, Strong Atiyah over the algebraic numbers extends to every field Qbar(z) and ranks are one-variable Galois invariant
distinct_from:
  atiyah-base-change-holds-off-a-countable-set: that shows the exceptional transcendental parameters form a countable set, with no determinant hypothesis; this proves, under the determinant conjecture, that the set is empty.
  determinant-conjecture-excludes-liouville-atiyah-exceptions: that excludes Liouville-type exceptional parameters through algebraic approximants of the parameter; this excludes every transcendental parameter through small integer polynomial values at it and a resultant identity, and supersedes it.
  strong-atiyah-base-change-algebraic-to-complex: that is the full base change for all complex coefficient fields; this proves it for fields of transcendence degree one that are purely transcendental over the algebraic numbers, under the determinant conjecture.
  vn-rank-galois-invariant-for-torsion-free-groups: that is the invariance statement for all complex coefficients; this establishes its one-variable case under the determinant conjecture and Strong Atiyah over the algebraic numbers.
artifacts:
  - research/artifacts/atiyah-one-variable-base-change-2026-09-12.md
---

**ESTABLISHED (unreviewed)** by [[one-variable-atiyah-base-change-proof]].

Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar` and Lueck's
determinant conjecture. Put `D = D_(Qbar[G])`, a skew field. For every
transcendental `z in C`:

1. `x -> z` embeds `D(x)` in `U(G)` as the division closure of `Qbar(z)[G]`;
2. every matrix over `Qbar(z)[G]` has integral von Neumann kernel dimension;
3. that dimension does not change when `z` is replaced by another transcendental
   number. In one variable this is exactly the Galois invariance of
   `vn-rank-galois-invariant-for-torsion-free-groups`.

Equivalently, the countable exceptional set `E_G` of
[[atiyah-base-change-holds-off-a-countable-set]] is empty.

**Mechanism.**
* **Reduction.** A kernel excess `kappa_0 > 0` at a transcendental `z_0` is moved,
  by linearization, padding and restriction of scalars, to a square pencil
  `M_0 + x M_1` over `Z[G]` that is full over `D(x)`.
* **Resultant identity.** For an irreducible integer polynomial `p` with leading
  coefficient `a` and roots `alpha_j`, the integral matrix
  `X = M_0 (x) E + M_1 (x) F` built from the companion pencil of `p` satisfies
  `Delta(X) = |a|^N prod_j Delta(M(alpha_j))`.
* **Polynomial inequality.** The determinant conjecture gives `Delta(X) >= 1`.
  With the bound `Delta(M(alpha)) <= C |alpha - z_0|^(kappa_0) max(1,|alpha|)^(N - kappa_0)`,
  this becomes `|p(z_0)| >= c M(p)^(-(N - kappa_0)/kappa_0)`.
* **Box principle.** Minkowski gives integer polynomials of degree `n` and height
  `H` with `|P(z_0)| <= H^(-n)` (real `z_0`) or `H^(-(n-1)/2)` (complex `z_0`).
  For large `n` this contradicts the polynomial inequality.

**Consequences.**
* **Master host.** Under `SA(E)` and `Det(E)` for the master host,
  `algebraic-atiyah-and-determinant-one-group-tester` transports both hypotheses
  to every torsion-free group. So every torsion-free group then satisfies Strong
  Atiyah over `Qbar(z)` for every complex `z`, with `z`-independent ranks.
* **The base change, reduced.** Under the determinant conjecture,
  `strong-atiyah-base-change-algebraic-to-complex` reduces to coefficient fields
  of transcendence degree at least 2, and to algebraic extensions of `Qbar(z)`.
  There the Kronecker analogue of the resultant identity loses a product of
  degrees (artifact, Section 6).
* **Nonsofic groups.** Neither hypothesis is known for any nonsofic group. The
  statement is a transfer theorem, not a new class of groups.

**Model tests.**
* For `G = Z/2`, the family `x(1+s)/2` has kernel `1/2` at every `z != 0`:
  without the skew field the conclusion fails.
* A self-adjoint `t` with an atom at `pi` makes `pi` exceptional for `Qbar(t)`,
  but no integral model obeys a determinant bound. Compare
  `serre-class-atoms-obey-degree-bound`.
* Sofic groups satisfy both hypotheses, and Jaikin-Zapirain's base change
  (GAFA 29 (2019), Theorem 1.1) gives the conclusion independently.

**Status.** Unreviewed. The argument uses only standard facts: Higman
linearization, Jacobson's normal form, the companion pencil, Minkowski's box
principle, and Fuglede--Kadison determinant properties from Lueck's book,
Theorem 3.14, not re-read here. The combination was not found in the sources
checked (artifact, final paragraph).
