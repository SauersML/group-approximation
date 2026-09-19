---
rg: 2
id: torus-degree-regularity-lifts-through-li-kernels-proof
kind: route
title: Restrict to the fixed torus of a normal subgroup, then lift regularity by Strebel's D(Z) on coset blocks, by nilpotent lifting mod p, and by residual separation
target: torus-degree-regularity-lifts-through-li-kernels
requires:
  - torus-automata-with-regular-degree-are-surjective
  - torus-automata-over-rf-or-domain-groups-are-surjunctive
  - torus-degree-regular-on-prime-power-residual-support
artifacts:
  - research/artifacts/torus-degree-li-kernel-descent-2026-09-19.md
---

Artifact Sections 0–4.

**Import (verbatim).** T. D. Cochran and S. Harvey, *Homology and derived series of groups*,
Geom. Topol. 9 (2005), pp. 2174–2175:

> "In [27, page 305], Strebel shows that, under the hypotheses of Lemma 4.4, if f is
> injective then f̃ is injective. There he shows that the class, D(Z), of groups Γ for which
> this property is satisfied includes torsion-free abelian groups and is closed under
> various natural operations such as extensions. Consequently, any PTFA group is in this
> class. This class of groups was previously called conservative and was later shown by J
> Howie and H Schneebli to coincide with the class of locally indicable groups [14]."

Here Lemma 4.4 concerns "f̃ : M → N ... a homomorphism between free ZΓ–modules" and
"f = f̃⊗ id ... M⊗ZΓ Z→N⊗ZΓ Z". The references are [14] Howie–Schneebeli, Manuscripta
Math. 44 (1983) 71–93, and [27] Strebel, Comment. Math. Helv. 49 (1974) 302–332.

1. **Fixed tori (Lemma 0.1).**
   - For any normal `N`, `Fix(N) ≅ (T^d)^(G/N)` and `tau_N` is an injective torus automaton
     over `G/N`.
   - Čech `H^1` of `(T^d)^S` is `Z[S]^d` by continuity over finite subproducts, as in C1.
   - The inclusion acts on `H^1` as `p_N`, so `D(tau_N) = p_N(D)`.
   - This is steps 1 and 3 of the route of
     `torus-automata-over-rf-or-domain-groups-are-surjunctive`, which do not use finite index.
   - For `N = G` the periodic-point lemma of that node gives `ε(D) in GL_d(Z)`.
2. **Invertibility (Lemma 0.2).** If `tau_N` has regular degree, it is onto by
   `torus-automata-with-regular-degree-are-surjective`. It is then a homeomorphism whose
   inverse is a torus automaton, and functoriality gives `p_N(D) in GL_d(Z[G/N])`.
3. **LI kernels (Theorem 1).**
   - `Z[G] = ⊕_t Z[N] t` over coset representatives. Right multiplication by `D` maps a
     finite block `P_(C_0) = ⊕_(t in C_0) Z[N]^d t` into `P_(C_1)`, left `Z[N]`-linearly,
     because `(η t)(D_s s) = (η D_s) t s`.
   - Applying `Z ⊗_(Z[N]) -` gives the restriction of `r_(p_N(D))` to the cosets `C_0`,
     which is injective.
   - Strebel's `D(Z) = LI` (import, converted to left modules by `g -> g^-1`) makes the block
     map injective. This excludes a kernel vector in the block.
4. **Locally normal `p` kernels (Theorem 2).**
   - Lift `p_N(D) E = I` to `D E' = I + X`. The entries of `X` lie in `Z[G] ω(P)` for a
     finite `p`-subgroup `P` normal in `G`.
   - `F_p[G] ω(P)` is a two-sided ideal with `k`-th power `F_p[G] ω(P)^k`. It is nilpotent
     because `ω(P)` is: induct through a central element of order `p`, which is also Lemma 2
     of the artifact of `torus-degree-regular-on-prime-power-residual-support`.
   - So `D` has a right inverse mod `p`. A kernel vector not divisible by `p` then reduces to
     zero, a contradiction.
   - Invertibility is needed: `1 + t` over `Z/2`.
5. **Series and residual separation (Lemma 3.1, Theorem 3, Corollary 3.2).**
   - `(tau_(N_1))_(N/N_1) = tau_N` at the level of degrees, by `p_(N/N_1) p_(N_1) = p_N`.
     Descent composes along finite series.
   - For a directed family `M_j <= N` of `G`-normal subgroups with trivial intersection and
     descent-admissible quotients `N/M_j`: pick `M_j` injective on `supp ξ`, and descend
     `p_N(D)` regular to `p_(M_j)(D)` regular. This contradicts `p_(M_j)(ξ) p_(M_j)(D) = 0`.
   - Finite nilpotent kernels are handled by their Sylow series. A finitely generated
     residually finite-nilpotent `N` is handled by its characteristic finite-index nilpotent
     residuals.
6. **Consequences (Section 4).**
   - *Extension closure.* `tau_N` is injective over `G/N`, so the regularity input is C2
     for `G/N`.
   - *Hosts.* Use `torus-automata-over-rf-or-domain-groups-are-surjunctive`(a) and
     `torus-degree-regular-on-prime-power-residual-support`(a) for the quotient.
   - *Reduction.* LI is local and extension-closed, so Zorn gives a maximal LI normal `M`,
     and `G/M` has trivial LI radical.
7. **Limit (Remark 2.3).** The Bezout element of
   `torus-degree-regular-on-prime-power-residual-support`(b) has `p_N(D) = 1` whenever the
   non-prime-power finite subgroup lies in `N`.
