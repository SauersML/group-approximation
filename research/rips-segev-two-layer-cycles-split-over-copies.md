---
rg: 2
id: rips-segev-two-layer-cycles-split-over-copies
kind: claim
title: In Steenbock's Rips--Segev core a relation alpha (u + w b) = 0 with u(1) + w(1) = 0 is a finite 1-cycle on the Cayley graph that splits as a sum of cycles c_C in finitely many copies of Gamma; each copy has at most one line of its cycle support whose coset no other copy's cycle touches, so this case reduces to a coefficient-free linked-cycle lemma, which holds for at most 14 copies and which the star family does not violate
distinct_from:
  rips-segev-coefficient-free-extremal-copy-lemma-fails: that kills the support-only extremal-copy lemma for arbitrary minimal coverings (star family); this replaces the covering by a family forced by alpha, in which every copy carries a nonzero cycle through at least 42 lines, so the star family is not an instance.
  rips-segev-port-holonomy-is-tautological-and-f2-blind: that shows the support condition depends on a chosen covering and ratio products carry no information; this removes the choice (the cycle picks the copies) and uses no ratios.
  rips-segev-three-copy-configurations-carry-no-zero-divisors: its rank-one lemma is the only coefficient input here; this applies it to lines untouched by the other copies' cycles, which are pure for every field.
  rips-segev-two-copy-configurations-carry-no-zero-divisors: its two-link lemma (two copies share at most 3 cosets) gives the 14-copy case of the linked-cycle lemma.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this is a strict reduction of the half u(1) + w(1) = 0 of its two-layer case to a statement about supports of cycles in copies.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-two-layer-cycles-split-over-copies-proof`.
Strict reduction, plus a calibration of the step it replaces.

**Setting.**  As in `rips-segev-three-copy-configurations-carry-no-zero-divisors`.
- `K` is Steenbock's core with `Gr'_*(1/8)` and `girth(Phi) >= 42`.  `Cay` is the Cayley graph of `K` on
  `{a, b}`, and a *copy* is `C = h g(Gamma) ⊆ Cay`.
- The lines of `Gamma` are the vertices of `Phi`, and its `b`-edges are the edges of `Phi`.
- Let `alpha (u + w b) = 0`, with `alpha != 0`, `w != 0` and `u, w in k[t^{±1}]`.  Put `X = alpha u` and
  `Y = alpha w`, so `X(z b) = -Y(z)`.
- On a left `<a>`-coset `T` write `alpha_T = z_T f_T(a)`, `P_T = f_T u` and `Q_T = f_T w`.

**Theorem.**  Assume `u(1) + w(1) = 0`.
1. *(Harmonic cycle.)*  The chain `c = sum_z Y(z) [z -> z b] + sum_T phi_T` is a finite nonzero 1-cycle on `Cay`
   over `k`.  Here `phi_T` is the chain on the `a`-edges of `T` with generating function `f_T (u + w) / (t - 1)`,
   a Laurent polynomial.
2. *(Splitting.)*  There are finitely many distinct copies `C_1, ..., C_N` and nonzero cycles `c_i in Z_1(C_i; k)`
   with `c = c_1 + ... + c_N`.
   - The splitting is unique iff `H_2(coned-off Cayley complex; k) = 0`.  Existence needs only that the relators
     are closed paths in `Gamma`.
3. *(Cycle lines.)*  The *cycle lines* `Lambda_i` of `c_i` are the lines of `C_i` meeting a `b`-edge of `supp c_i`.
   - They are the vertices of a subgraph of `Phi` of minimum degree `>= 2`.  So `|Lambda_i| >= girth(Phi) >= 42`,
     and they lie in pairwise distinct cosets.
4. *(Untouched lines are pure.)*  Call a cycle line of `C_i` *untouched* if no `c_j`, `j != i`, is nonzero on an
   edge with an endpoint in its coset `T`.
   - Then `T` is active.  Its ports lie in the distinguished positions of that line: `supp P_T ⊆ In`,
     `supp Q_T ⊆ Out`.
   - By the rank-one lemma, all untouched cycle lines of all copies have one line index of `Gamma`.  So each copy
     has at most one.
5. *(Reduction.)*  Consider the **linked-cycle lemma (LC):** for every finite family of distinct copies with nonzero
   cycles `c_i in Z_1(C_i)`, some `C_i` has two untouched cycle lines.
   - LC implies that `k[K]` has no relation `alpha (u + w b) = 0` with `alpha, w != 0` and `u(1) + w(1) = 0`,
     over any field `k`.  The same holds in `k[G]`.
   - LC is coefficient-free: it speaks only of the supports of cycles in copies.
6. *(Small families.)*  LC holds for `N <= 14`.  A touched cycle line of `C_i` lies in a coset shared with some
   `C_j`, and two copies share at most 3 cosets (two-link lemma).  So at most `3(N - 1) <= 39` of the `>= 42` cycle
   lines are touched.
   - So a counterexample with `u(1) + w(1) = 0` has at least 15 copies in every splitting of its cycle.
7. *(Star family.)*  The star family of `rips-segev-coefficient-free-extremal-copy-lemma-fails` is not a
   counterexample to LC.  Each of its copies meets the others in only 9 cosets, so at least 33 of the `>= 42` cycle
   lines of any cycle it carries are untouched.

**Calibration (why the step "support matching alone, over `F_2`" is blocked).**
- In `H = <a, b | (a^m b)^n>` with `n >= 3`, put `x = a^m b`.  Then `alpha = sum_{j<n} x^j` and
  `u + w b = 1 - a^m b` give `alpha (u + w b) = 1 - x^n = 0`, over every field.
- This model satisfies every hypothesis the step allows:
  - the active coset graph is a simple directed `n`-cycle with in- and out-degree 1;
  - `X(z b) = -Y(z)` holds;
  - the rank-one identities `P_T Q_T' = P_T' Q_T` hold;
  - every coset is locally rigid;
  - the forced product around the cycle is consistent;
  - `u(1) + w(1) = 0`.
- Its splitting is one copy, the relator loop, in which every line is untouched and pure.
- It differs from `K` in two facts: all its lines have one row (the lines of `Gamma` have distinct rows), and
  `u/w` is a monomial (which torsion-freeness excludes in `K`).  A proof must use some fact the model violates.
- So neither half of the proposed step can close from simplicity, degrees, rank-one identities and rigid-cycle
  holonomy alone.  Row distinctness has to enter, and here it enters through statement 4.

**Open.**
- LC for `N >= 15`, via an extremal (outermost) copy in a finite family of copies linked along shared cosets.
- The half `u(1) + w(1) != 0`.  There `alpha(1) = 0` is forced, but the harmonic chain has rays along the cosets
  with `f_T(1) != 0`.
