---
rg: 2
id: kadison-kaplansky-torsion-free
kind: claim
title: The reduced group C*-algebra of every torsion-free group has no nontrivial projections (Kadison--Kaplansky)
root: true
refuted_by:
  - kadison-kaplansky-counterexample-exists
distinct_from:
  rank-one-lattice-kadison-kaplansky-and-charzero-idempotents: that establishes this conclusion for torsion-free real-rank-one lattices through Baum--Connes; this is the conjecture for every torsion-free group.
  strong-atiyah-torsion-free: that asserts integrality of von Neumann kernel dimensions of matrices over K[G]; this asserts that C*_r(G) has no projection other than 0 and 1. Over C, Strong Atiyah makes spectral measures of non-scalar self-adjoint elements of C[G] atomless, while this makes their supports intervals; neither is known to imply the other.
  kaplansky-zero-divisor-conjecture: that is the algebraic domain conjecture for K[G] over all fields; this is the analytic idempotent conjecture in C*_r(G), whose algebraic consequence is the characteristic-zero idempotent conjecture.
---

**Conjecture (Kadison--Kaplansky).** Let `G` be a countable torsion-free
group. Then the reduced group C*-algebra `C*_r(G)` contains no projection
other than `0` and `1`.

Equivalent forms:
- no idempotent other than `0` and `1`, since every idempotent in a unital
  C*-algebra is similar to a projection;
- by `reduced-projection-iff-gapped-spectral-measure`, every self-adjoint
  `a` in `Z[i][G]` has a spectral measure, for the canonical trace, whose
  support is an interval.

The torsion-free hypothesis is necessary: for a finite subgroup `F` of order
`n > 1`, the element `(1/n) sum_(f in F) f` is a projection of trace `1/n`.

Taking the spectral form with `a` in `Z[i][G]`, a counterexample for `G` is
witnessed inside `C*_r(H)` for the finitely generated subgroup `H` generated
by the support of `a`. So the conjecture holds for all torsion-free groups iff
it holds for all finitely generated torsion-free groups.

## Known cases, and the mechanism behind them

- **Kaad--Proietti.** If the Baum--Connes assembly map of a torsion-free group
  is surjective, `C*_r(G)` has no nontrivial idempotents. This is Kaad--Proietti,
  Kyoto J. Math. 62 (2022), Corollary 1.6, as recorded and checked in
  `rank-one-bcc-implies-charzero-idempotent-proof`.
- **Classical route.** Traces of classes in the image of the assembly map are
  integers for torsion-free groups (Atiyah's L^2-index theorem, organized by
  Lück, Invent. Math. 149 (2002)). A faithful trace taking integer values on
  projections leaves only `0` and `1`. That paper was not re-read here.
- **Groups where assembly is known to be surjective**, among others:
  - a-T-menable groups (Higson--Kasparov);
  - hyperbolic groups (Mineyev--Yu; Lafforgue);
  - real-rank-one lattices (`real-rank-one-lattices-bcc-finite-wreath-products`).
- **Algebraic consequence.** The conjecture for `G` gives Kaplansky's
  idempotent conjecture for `k[G]`, `char k = 0`. The argument is the one in
  `rank-one-bcc-implies-charzero-idempotent-proof`.

**Matrix form.** A gap in the spectral measure of a self-adjoint `n x n` matrix
over `C[G]` gives a projection in `M_n(C*_r(G))` of trace strictly between `0`
and `n`. When that trace is not an integer, it refutes the torsion-free trace
conjecture, and so Baum--Connes surjectivity for `G`. It does not by itself
refute this root.

## Attempts

- **Where a counterexample must live.**
  - `G` must be torsion-free, and assembly must fail to be surjective for it,
    by the contrapositive of Kaad--Proietti. So `G` is not a-T-menable, not
    hyperbolic, and not a real-rank-one lattice.
  - The failure passes up: `C*_r(H)` sits inside `C*_r(G)` for every subgroup
    `H`, so a counterexample subgroup makes every overgroup a counterexample.
- **Kun--Thom actors in characteristic p: dead as hosts.** The Theorem E
  groups `EL_r(F_q[x^(+-1)]) semidirect SL_d(Z)` contain root elements of
  order `p` (`kun-thom-actors-have-no-torsion-free-finite-index-subgroups`).
  A torsion-free subgroup meets every root subgroup trivially, so it contains
  no Theorem E Kazhdan subgroup `Gamma`.
- **Compressions as a source of isometries: dead.** `C*_r(G)` carries a
  faithful tracial state, so every isometry `s` in `M_n(C*_r(G))` is unitary:
  `tau(1 - s s*) = tau(s* s) - tau(s s*) = 0` with `1 - s s* >= 0`. A
  compression `t Gamma t^-1 < Gamma` acts on `C*_r(Gamma)` by the unital
  trace-preserving endomorphism `Ad lambda(t)`. So it only relates projections
  of equal trace. It cannot create a projection of non-integer trace, and the
  rigid defect machinery supplies no projections here.
- **Kazhdan projections: dead.** For an infinite Kazhdan group, the Kazhdan
  projection lives in `C*_max(G)` and maps to `0` in `C*_r(G)`, because the
  trivial representation is not weakly contained in the regular one. A
  sum-of-squares identity `(a - c)^2 - eps^2 = sum x_i* x_i` in `C[G]`
  certifies a gap in the MAXIMAL spectrum only. A reduced projection also needs
  reduced spectral mass on both sides of the gap. For the Laplacian of a
  non-amenable group, the reduced spectrum sits entirely above the Ozawa gap
  (Kesten).
- **Both dead ends are in the graph as an established claim:**
  `subgroup-average-projections-give-no-reduced-bc-obstruction`
  (baum-connes-leavitt, 5c522cf99). Kazhdan projections of infinite subgroups
  vanish in `C*_r(G)`, compression relations collapse to equality under the
  faithful trace, and averages over finite subgroups are trivial for
  torsion-free groups.
- **Lattice transfer: a live shape, but for the matrix trace form only.**
  - *Setup.* Suppose `G` and a torsion-free `Gamma` act freely and cocompactly
    on one complex `X`.
  - *Transfer.* A gap projection `P = chi_[0,c](Delta_k)` of the combinatorial
    Laplacian lies in both `M_n(C*_r(G))` and `M_m(C*_r(Gamma))`. Because its
    diagonal is `Aut(X)`-invariant, `tau_Gamma(P) = r tau_G(P)` with
    `r = |Gamma\X_0| / |G\X_0|`. This extends the proof of
    `free-cocompact-lattices-proportional-l2-betti`, as observed by the
    atiyah-computability lane.
  - *Conclusion.* A non-integer `r tau_G(P)` refutes the torsion-free trace
    conjecture for `Gamma`. It does not by itself give a 1x1 counterexample to
    this root.
  - *Existence.* The complex, which needs non-discrete `Aut(X)`, is the open
    `complex-with-irrational-and-torsion-free-lattices`.
- **Torsion-free Kazhdan hosts, no mechanism yet.**
  - Fournier--Facio's torsion-free nonsofic group (`fournier-facio-group-is-nonsofic`).
  - Torsion-free finite-index subgroups of `EL_3(Z[x_1,...,x_d])`: Kazhdan by
    Ershov--Jaikin-Zapirain, and virtually torsion-free by Selberg's lemma.
  Baum--Connes is not known for either, and even `SL_3(Z)` is open. No
  construction of a gapped spectral measure is known for them. Nonsoficity
  obstructs approximation arguments, not the conjecture.
