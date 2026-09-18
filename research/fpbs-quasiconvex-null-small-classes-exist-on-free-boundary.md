---
rg: 2
id: fpbs-quasiconvex-null-small-classes-exist-on-free-boundary
kind: claim
title: The boundary of F_2 carries an ergodic nonatomic quasi-invariant class (a symmetric odometer code with killing words) that is singular to every Dini measure, contains no shadow-summable measure, and is null on the orbit of the limit set of every infinite-index finitely generated subgroup; since F_2 has no BB certificate, the three known boundary filters (Dini, shadow, quasiconvex-null) cannot by themselves prove that no hyperbolic group has one
distinct_from:
  fpbs-rotation-boundary-class-refutes-shadow-summability: that builds a non-shadow-summable class by an irrational-rotation code inside a Schottky subgroup, which lies in the limit set of that subgroup and so is killed by the quasiconvex-limit-set theorem in every group containing it properly; this builds a non-shadow-summable class that gives zero mass to the orbit of every such limit set, using an odometer (not a rotation) and killing words for every finite non-covering Stallings graph.
  fpbs-dini-singular-boundary-classes-exist-but-one-way-die: that constructs Dini-singular one-way and paperfolding classes and shows they are shadow-summable (and their languages sit in a non-covering Stallings graph); this class is Dini-singular, not shadow-summable, and escapes every non-covering Stallings graph.
  fpbs-quasiconvex-limit-set-classes-are-never-pdr: that proves a certificate's class must be null on every quasiconvex limit-set orbit and names the existence of quasiconvex-null small classes as its open statement; this answers that statement positively on F_2.
---

**ESTABLISHED for `F_2` (written proof; see
`research/fpbs-quasiconvex-null-small-classes-exist-on-free-boundary-proof.md`; script
`experiments/quasiconvex-null-classes-2026-09-17/odometer_code.py` with output `odometer_code.out`).**
The proof is self-contained apart from standard facts: Perron--Frobenius, Birkhoff's ergodic theorem, unique
ergodicity of the dyadic odometer, Stallings folding, and the definitions and Theorem C of
`fpbs-dini-boundary-class-diagonal-dissipative`. The general hyperbolic case is **open** (see below).

**Why this matters for the flagship.** The named open statement of `fpbs-quasiconvex-limit-set-classes-are-never-pdr`
asks whether a boundary class can pass all three filters that previous lanes proved every BB certificate must pass:
- singular to every Dini measure (`fpbs-dini-boundary-class-diagonal-dissipative`, Theorem C);
- no measure in the class is shadow-summable (Theorem A there, and the one-way claim);
- null on `Gamma Lambda_H` for every infinite-index quasiconvex `H` (Corollary 4 of the quasiconvex claim).

If no class passed all three, no hyperbolic group would have a BB certificate. This claim shows that on `F_2` such a
class exists. But `F_2` has cost 2, so by Bevilacqua--Bowen's Theorem 8.1 it has no BB certificate at all. So the
class passes all three filters and still carries no certificate. Hence **the statement "no hyperbolic group has a BB
certificate" cannot be derived from these three filters**, even on `F_2`. A fourth mechanism is needed.

## Theorem

Let `F_2 = <a, b>` act on its boundary `dF_2`, the space of infinite reduced words. There is a Borel probability
measure `nu_0` on `dF_2` such that its quasi-invariant class `[nu] = [sum_g c_g g_* nu_0]` (with `c_g > 0`,
`sum c_g = 1`) has the following properties.

1. **Ergodic and nonatomic.**
2. **Quasiconvex-null.** `nu(Lambda_H) = 0`, hence `nu(F_2 Lambda_H) = 0`, for every finitely generated subgroup
   `H` of infinite index. (In `F_2` these are exactly the infinite-index quasiconvex subgroups.)
3. **No shadow-summable measure.** For every probability `lambda ~ nu` and every `s >= 0`,
   `S_s(lambda) = sum_g lambda(O_s(g)) lambda(O_s(g^{-1})) = infinity`.
4. **Dini-singular.** `nu` is singular to every Dini measure.

**Construction.** Let `Omega = lim Z/2^{n+2}` be the dyadic odometer with Haar measure `m` and translation `x -> x+1`.
Build a Borel labelling `F : Omega -> {a, a^{-1}, b, b^{-1}}` with three features:
- **parity types**: `F(y)` is `a`-type for even `y` and `b`-type for odd `y`, so every window is an alternating,
  hence reduced, word;
- **odd symmetry**: `F(-y) = F(y)^{-1}`;
- **killing words**: at sparse stages `n_j`, a window of length `l_j` is overwritten by a word `k_j` and its mirror by
  `k_j^{-1}`. Here `k_j` is an alternating word that is readable from no vertex of `Delta_1, ..., Delta_j`, and
  `(Delta_i)` enumerates all finite connected folded non-covering labelled graphs.

The remaining positions are filled hierarchically, Toeplitz style. The overwrites have summable density, so `F` is
defined a.e. Put `zeta(x) = F(x+1) F(x+2) F(x+3) ...` and `nu_0 = zeta_* m`.

The four mechanisms are these.
- **Ergodicity.** `zeta(x+1) = F(x+1)^{-1} zeta(x)`, and the odometer is ergodic.
- **Quasiconvex-null.** A ray in `Lambda_H` has a tail readable in the Stallings core of a conjugate of `H`. That core
  is some `Delta_i`. But a.e. ray contains `k_i` in every tail, by Birkhoff.
- **Killing words exist** (Lemma 1). For a finite folded non-covering graph, the alternating-walk transfer matrix has
  spectral radius `< 2`, by a Perron--Frobenius and bijection argument.
- **Not shadow-summable.** The involution `tau_m(x) = -x-m-1` preserves `m` and inverts length-`m` prefixes. So by
  Cauchy--Schwarz over the `O(m)` cells at scale `2^N ~ Km`, together with equidistribution of `-(m+1)` in the
  odometer, the `m`-th term of `S_0(lambda)` is `>= c/m`.

## Can the class carry a PDR imp action?

Not on `F_2`, and not for a reason any of the three filters sees.
- The boundary action of `F_2` is amenable. So the Maharam extension of `[nu]`, and every imp action whose Zimmer
  boundary class is `[nu]`, is an amenable imp action.
- If one of these actions were ergodic and PDR with infinite nonatomic components, Bevilacqua--Bowen's Theorem 8.1
  would give `F_2` fixed price 1. But `F_2` has cost 2 (Gaboriau).
- Hence no BB certificate of `F_2` has Zimmer class `[nu]`. Yet `[nu]` passes all three filters.

The honest conclusion is a **class-killing obstruction for a proof strategy**. The strategy was: "show that every
boundary class passing the Dini, shadow and quasiconvex-null filters is empty, hence no hyperbolic group has a BB
certificate". This claim kills that strategy. Any proof that a hyperbolic group has no certificate must use a property
of the certificate that goes beyond those three filters. The mechanism that excludes `[nu]` on `F_2` is, for now, only
the global cost argument.

## Calibration (script `experiments/quasiconvex-null-classes-2026-09-17/odometer_code.py`, output `odometer_code.out`)

- **Lemma 1, checked.** There are 26131 connected folded non-covering graphs with at most 4 vertices. The largest
  spectral radius of the alternating transfer matrix among them is `1.798907 < 2`.
- **A killing word, found.** A shortest alternating word readable from no vertex of any of the 703 graphs with at most
  3 vertices has length 12: `abaBaBABabaB`.
- **Finite-stage code, checked.** For the code on `Z/2^15`, with one inserted killing word:
  - there are 0 non-reduced adjacent pairs and 0 symmetry failures;
  - the inversion identity `prefix_m(x)^{-1} = prefix_m(-x-m-1)` holds in 2972 of 2972 samples;
  - the number of cells is between `4m` and `7.75m`.
- **Shadow terms, checked.** The Haar shadow term `T_m = sum_{|w|=m} f(w) f(w^{-1})` satisfies `m T_m in
  [0.167, 0.250]` for `m = 1, 2, 4, ..., 1024`. So `T_m ~ 1/m`, and the shadow sum diverges logarithmically, as item 3
  predicts.

## Named open statements

1. **General hyperbolic `Gamma` (the flagship case, cocompact `Sp(n,1)` lattices).** Do quasiconvex-null small classes
   exist?
   - Any coding by a finite alphabet inside a Schottky subgroup `F` lands in `Lambda_F`, and is killed by
     `fpbs-quasiconvex-limit-set-classes-are-never-pdr`.
   - The natural transplant is a symmetric odometer code into Cannon's geodesic automaton, i.e. the sofic shift of
     geodesic words. Two things are needed:
     - killing words for every finite quasiconvex core (a coset-automaton analogue of Lemma 1: spectral radius below the
       growth rate);
     - an inversion involution `tau_m` compatible with the automaton.
   - The obstacle is gluing: the concatenation of geodesic blocks must stay uniformly quasi-geodesic, and the reversed
     block must be readable in the automaton.
2. **The fourth mechanism.** Find a property of BB certificates that excludes `[nu]` on `F_2` without cost. Two
   candidates:
   - **Odometer match rigidity.** Show that `zeta` is a.e. injective, so `g zeta(x) = zeta(x')` forces
     `x' in x + Z`. Then prove the diagonal of any imp action over `[nu]` is dissipative, as in Theorem 3 of
     `fpbs-rotation-boundary-class-refutes-shadow-summability`.
   - **Theorem 2 of `fpbs-quasiconvex-limit-set-classes-are-never-pdr` for an infinitely generated `L`.** Here `L` would
     be a subgroup whose limit set has private points of positive `nu` mass.
   - If either works uniformly, it is the next filter to transplant to lattices.

## Attempts

- 2026-09-17, w10-026: first a Glimm--Effros product block code was tried, as the brief suggested. It is not closed under
  inversion, and the shadow sum then converges, because words and their inverses never share cells. A pure Toeplitz code
  was tried next. Its hole runs cannot host growing killing words. The odometer with overwrites fixes both problems:
  - odd symmetry gives the involution `tau_m`;
  - scale choice gives `O(m)` cells;
  - summable overwrites carry the killing words.
