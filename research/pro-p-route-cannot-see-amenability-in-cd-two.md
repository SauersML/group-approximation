---
rg: 2
id: pro-p-route-cannot-see-amenability-in-cd-two
kind: claim
title: A torsion-free lattice in SL_3(Q_2) has cd 2, chi = V >= 1, b_1 = 0 on every finite cover and only finite or p-adic analytic pro-p completions, so it meets every mod-p, cup-product and Golod-Shafarevich constraint on a cd-2 amenable counterexample; these constraints cannot refute chi >= 1
distinct_from:
  amenable-cd-two-pro-p-completions-not-golod-shafarevich: that derives the mod-p and Golod-Shafarevich constraints on a counterexample; this exhibits a non-amenable group of type F that satisfies all of them with chi > 0 and so kills that route and its cup-product and pro-p refinements as a way to refute chi >= 1
  pgl3-nonarchimedean-lattices-have-property-t: that proves property (T) for lattices in PGL_3 of a local field; this uses it together with congruence subgroup property and building combinatorics to compute the homology, pro-p completions and p-goodness of one torsion-free lattice
  rf-weak-bass-defect-is-degree-two-approximation-defect: that reduces the residually finite case to Lück approximation in degree 2 for amenable groups; this shows the profinite side of that reduction cannot distinguish an amenable counterexample from a Kazhdan lattice, so the missing input is L2 or Følner information
---

**ESTABLISHED** (proposed; referee pending) through `pro-p-route-cannot-see-amenability-in-cd-two-proof`.
The heaviest import is the congruence subgroup property: the congruence kernel is finite for
S-arithmetic subgroups of S-rank `>= 2` of special unitary groups of hermitian forms over a
quadratic extension. See Prasad–Rapinchuk, *Developments on the congruence subgroup problem after
the work of Bass, Milnor and Serre* (2010), §6, which credits Rapinchuk and Tomanov. The other
imports are standard: strong approximation, Borel–Harish-Chandra, Kazhdan's property (T) via
`pgl3-nonarchimedean-lattices-have-property-t`, Lazard, and Zelmanov (a GS pro-p group contains
a free pro-p subgroup of rank 2).

**The group.** Let `E = Q(√−7)`. The prime `2` splits in `E`, because `−7 ≡ 1 mod 8`. Let
`h = x x̄ + y ȳ + z z̄` on `E³`, let `G = SU(h)`, and put `S = {∞, 2}`. Then `G(R) = SU(3)` is
compact and `G(Q_2) ≅ SL_3(Q_2)`. Let `Γ` be a torsion-free subgroup of finite index in
`G(Z[1/2])`, for instance its principal congruence subgroup of level 3. Then `Γ` is a cocompact
lattice in `SL_3(Q_2)`. Let `Δ` be the Bruhat–Tits building of `SL_3(Q_2)` and `V` the number of
`Γ`-orbits of vertices.

1. **Type F, cd 2, positive Euler characteristic.** `Γ` acts freely and cocompactly on `Δ`.
   `Γ\Δ` is a finite aspherical 2-complex with `V` vertices, `7V` edges and `7V` triangles. So
   `cd Γ = 2` and `χ(Γ) = V >= 1`. Collapsing a maximal tree gives an aspherical presentation with
   `6V + 1` generators and `7V` relators, whose relation module is free of rank `7V`.
2. **The rational profile of a counterexample, at every finite index.** `Γ` has (T), so for every
   finite-index `N <= Γ`,

   > `b_1(N; Q) = 0`, `b_2(N; Q) = V [Γ:N] − 1`, `b_2^{(2)}(Γ) = V`.

   With `b_2(Γ) = V − 1`, this is exactly `χ = 1 + b_2`, `b_1 = 0`, which is the profile of a
   counterexample to Kropholler's question in dimension 2 with finite abelianization, as in item 4
   of `amenable-cd-two-pro-p-completions-not-golod-shafarevich`. For `Γ` it holds with error `0`
   at every finite index, not just `O(√index)`.
3. **Pro-p completions.** For every finite-index `N <= Γ` and every prime `p`, the pro-p
   completion `N_p̂` is finite if `p = 2`, and p-adic analytic if `p` is odd. In particular no
   `N_p̂` is Golod–Shafarevich. So `Γ` satisfies items 1 and 2 of
   `amenable-cd-two-pro-p-completions-not-golod-shafarevich` verbatim, with `χ = V`:

   > `1 − b_1(N; F_p) + b_2(N; F_p) = V [Γ:N]` and `b_1(N; F_p) <= 2 + 2 √(V [Γ:N])`.
4. **No p-goodness.** No finite-index `N <= Γ` is p-good with `N_p̂` infinite, for any `p`. The
   reason is that a p-good `N` with infinite `N_p̂` would make `N_p̂` torsion-free analytic of
   `cd <= 2` with `χ = V [Γ:N] > 0`, while every such group has `χ = 0`.
5. **Obstruction.** Consider any argument that proves `χ_Q(K) <= 0` from these hypotheses:
   - `K` is finitely generated, residually finite, of type F, with `cd K = 2`;
   - no finite-index subgroup of `K` has a Golod–Shafarevich pro-p completion, for any `p`;

   together with anything these imply for groups in general. That includes the exact mod-p Euler
   identities, the Bass/Swan structure of `Z[F] ⊗ P` over finite quotients, the mod-p cohomology
   rings `H^*(N; F_p)` with cup products, Massey products, Bocksteins, restriction and transfer,
   and every weighted or Zassenhaus-degree refinement of the Golod–Shafarevich inequality. Such an
   argument would give `χ(Γ) <= 0`, so it is false. In particular:
   - (a) *The cup-product step fails.* `Γ` has both `b_1(N; F_p) = O(√[Γ:N])` and
     `b_2(N; Q) = V[Γ:N] − 1` in every finite cover. Its cup product
     `Λ² H^1(N; F_p) → H^2(N; F_p)` is that of a group, and no contradiction comes out.
   - (b) *The pro-p fallback is not decisive.* By item 4, a positive answer to "does an infinite
     finitely generated pro-p group of cd 2 with `χ > 0` have a Golod–Shafarevich open subgroup?"
     would only show that a counterexample has no p-good finite-index subgroup with infinite pro-p
     completion. `Γ` has that property for every `p` and still has `χ = V > 0`.
6. **What amenability must contribute.** A refutation of `χ >= 1` has to use a consequence of
   amenability that `Γ` violates. Two are known:
   - `b_2^{(2)} = 0`. This is what makes `D(P) = χ` in
     `amenable-cd-two-bass-defect-equals-euler-characteristic`. For `Γ` the relation module is free
     and `D(P) = 0`. It is the content of this node's target.
   - Failure of property (τ) for every infinite family of finite quotients (Lubotzky–Weiss).
     `Γ` has (T), so all its finite quotients form expanders.

   So any profinite argument must use Følner-type non-expansion of the finite quotients, and not
   just their mod-p cohomology. Along a residual chain, `Γ` satisfies Lück approximation,
   `b_2(N_i)/[Γ:N_i] → V = b_2^{(2)}(Γ)`. An amenable residually finite counterexample `K` would
   violate it, with `b_2(N_i)/[K:N_i] → χ >= 1` while `b_2^{(2)}(K) = 0`. This is the degree-2
   approximation target of `rf-weak-bass-defect-is-degree-two-approximation-defect`, and the
   missing input for it is not profinite.

**Calibration.** The construction is the arithmetic source of Mumford's fake projective plane
(Mumford 1979). His lattice in `PGL_3(Q_2)` acts simply transitively on vertices, so it has
`V = 1`, 7 generators, 7 relators and `χ = 1`. The count `χ = V(1 + (q² + q + 1)(q − 2)/3)` for
buildings of thickness `q + 1` gives `χ = V` at `q = 2`. It is positive for every `q >= 2`, so
lattices in `SL_3(Q_p)` for any `p` behave the same way. In every case the non-amenable group has
the counterexample profile, and it does so only because `b_2^{(2)} > 0`.
