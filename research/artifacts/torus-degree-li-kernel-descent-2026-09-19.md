# Degree regularity of injective torus automata descends through locally indicable kernels

swarm-0917-w14-w14-gs-pull, 2026-09-19. Node: `injective-torus-automata-have-regular-degree` (C2).
Claim: `torus-degree-regularity-lifts-through-li-kernels`.

## 0. Conventions

- `G` is a countable group and `d >= 1`. `X_d(G) = (T^d)^G` carries the left shift
  `(g x)_h = x_(g^-1 h)`.
- A *torus automaton over `G`* is a continuous `G`-equivariant self-map `tau` of `X_d(G)`.
  - By `torus-automata-with-regular-degree-are-surjective` (C1),
    `tau^* : H^1(X_d(G); Z) = Z[G]^d -> Z[G]^d` is `xi -> xi D` for a unique
    `D = D(tau) in M_d(Z[G])`.
  - Vectors are rows. Write `r_D` for `xi -> xi D`.
  - `D` is *regular* if `r_D` is injective on `Q[G]^d`, equivalently on `Z[G]^d`
    (clear denominators).
- For `N <| G`, `p_N : Z[G] -> Z[G/N]` is the projection, applied entrywise to vectors and
  matrices.
- C2 for `G`: every injective torus automaton over `G`, at every `d`, has regular degree.
  Let `𝒞` be the class of groups satisfying C2.
  - By C1, every `G in 𝒞` is torus-surjunctive.
  - Conversely, if `tau` is bijective, its inverse is a torus automaton, and functoriality
    gives `D(tau) in GL_d(Z[G])` (Lemma 0.2), which is regular.
  - So `𝒞` is exactly the class of torus-surjunctive groups (all `d`).

**Lemma 0.1 (fixed tori of arbitrary normal subgroups).** Let `N <| G` be any normal subgroup,
of finite or infinite index.
- (i) `Fix(N) = {x : n x = x for all n in N}` is the set of `x` constant on the cosets of
  `N`. The map `iota : X_d(G/N) -> Fix(N)`, `iota(y)_h = y_(hN)`, is a
  `G`-equivariant homeomorphism, with `G` acting on `X_d(G/N)` through `G/N`.
- (ii) An injective torus automaton `tau` over `G` preserves `Fix(N)`. The map
  `tau_N = iota^-1 tau iota` is an injective torus automaton over `G/N`.
- (iii) `D(tau_N) = p_N(D(tau))`.

*Proof.*
1. *(i).* `(n x)_h = x_(n^-1 h)`, so `n x = x` for all `n` means `x_(nh) = x_h` for all
   `n, h`, that is, `x` is constant on the cosets `N h = h N`. The map `iota` is a continuous
   bijection of compact Hausdorff spaces, hence a homeomorphism, and it is equivariant.
2. *(ii).* If `x in Fix(N)`, then `n tau(x) = tau(n x) = tau(x)`. The map `tau_N` is
   continuous, injective and `G/N`-equivariant.
3. *(iii), the cohomology.* For any countable set `S`, `X_d(S) = (T^d)^S` is the inverse
   limit of the tori `(T^d)^F` over finite `F ⊂ S`. By continuity of Čech cohomology,
   `H^1(X_d(S); Z) = colim_F Z^(dF) = Z[S]^d`. The basis vector `e_(s,i)` is the class of the
   coordinate character `x -> x_s^(i)`. This is the computation of C1, with the index set `G`
   replaced by `S = G/N`.
4. *(iii), the pullback.* `iota^*` sends the class of `x -> x_h^(i)` on `X_d(G)` to the class
   of `y -> y_(hN)^(i)`, so `iota^* = p_N` on `Z[G]^d`.
5. *(iii), the degree.* From `tau iota = iota tau_N` we get
   `tau_N^* iota^* = iota^* tau^*`, that is, `tau_N^*(p_N xi) = p_N(xi D) = p_N(xi) p_N(D)`.
   Since `p_N` is onto, `D(tau_N) = p_N(D)`. QED.

This is steps 1 and 3 of the route of `torus-automata-over-rf-or-domain-groups-are-surjunctive`.
Finiteness of `G/N` is used there only in the invariance-of-domain step 2, which we do not use
except at `N` of finite index.

**Lemma 0.2 (bijective automata have invertible degree).** If a torus automaton `sigma` over a
group `K` is bijective, then `D(sigma) in GL_d(Z[K])`.

*Proof.* `sigma` is a continuous bijection of a compact Hausdorff space, so its inverse `rho`
is continuous and `K`-equivariant, hence a torus automaton with degree `E`. Then
`(rho sigma)^* = sigma^* rho^*` is `xi -> (xi E) D(sigma)`, and it equals the identity. So
`E D(sigma) = I`, and symmetrically `D(sigma) E = I`. QED.

**Lemma 0.3 (series).** Let `N_1 <= N` be normal subgroups of `G` and `tau` an injective torus
automaton over `G`.
- `tau_(N_1)` is an injective torus automaton over `G/N_1`, of degree `p_(N_1)(D)`.
- Its restriction to the fixed torus of the normal subgroup `N/N_1` of `G/N_1` has degree
  `p_(N/N_1)(p_(N_1)(D)) = p_N(D)`.

*Proof.* Apply Lemma 0.1 twice, and use `p_(N/N_1) p_(N_1) = p_N`. QED.

## 1. Locally indicable kernels reflect regularity (pure algebra)

**Import (Strebel; Howie–Schneebeli), verbatim.** From T. D. Cochran and S. Harvey,
*Homology and derived series of groups*, Geom. Topol. 9 (2005), pp. 2174–2175, read
2026-09-19 from the journal PDF:

> "Lemma 4.4 Suppose f̃ : M → N is a homomorphism between free ZΓ–modules with Γ PTFA and let
> f = f̃⊗ id be the induced homomorphism of abelian groups M⊗ZΓ Z→N⊗ZΓ Z. Then
> rankKΓ (image f̃)≥ rankQ(image f). In [27, page 305], Strebel shows that, under the
> hypotheses of Lemma 4.4, if f is injective then f̃ is injective. There he shows that the
> class, D(Z), of groups Γ for which this property is satisfied includes torsion-free abelian
> groups and is closed under various natural operations such as extensions. Consequently, any
> PTFA group is in this class. This class of groups was previously called conservative and was
> later shown by J Howie and H Schneebli to coincide with the class of locally indicable groups
> [14]."

> "[14] J Howie, H R Schneebeli, Homological and topological properties of locally indicable
> groups, Manuscripta Math. 44 (1983) 71–93 MR709846"

> "[27] R Strebel, Homological methods applied to the derived series of groups, Comment. Math.
> Helv. 49 (1974) 302–332 MR0354896"

**What is used (S).** If `Γ` is locally indicable, `f̃ : M -> M'` is a homomorphism of free
`ZΓ`-modules, and `f̃ ⊗ id : M ⊗_(ZΓ) Z -> M' ⊗_(ZΓ) Z` is injective, then `f̃` is injective.

- We apply (S) only to finitely generated free modules, the most restrictive reading.
- Cochran–Harvey use right modules, and we use left ones. The anti-automorphism `a -> a*` of
  `Z[Γ]`, `γ -> γ^-1`, converts a left module `M` into a right module `M*` (`m·a = a* m`).
  - Free modules go to free modules, and left-linear maps to right-linear maps.
  - `Z ⊗_(ZΓ) M = M*⊗_(ZΓ) Z`, since `ε(a*) = ε(a)`.

  So (S) holds verbatim for left modules and `Z ⊗_(ZΓ) -`.

**Theorem 1.** Let `N <| G` be locally indicable and `D in M_d(Z[G])`. If `p_N(D)` is regular
over `Q[G/N]`, then `D` is regular over `Q[G]`.

No automaton appears. `N` may have infinite index, and `G/N` is arbitrary.

*Proof.*
1. *Coset blocks.*
   - Fix a set `T` of representatives of the cosets `N t` of `N` in `G`. Then
     `Z[G] = ⊕_(t in T) Z[N] t` as left `Z[N]`-modules.
   - For finite `C ⊂ T` put `P_C = ⊕_(t in C) Z[N]^d t`, a free left `Z[N]`-module of rank
     `d|C|`.
   - Every vector of `Z[G]^d` lies in some `P_C`.
2. *`r_D` on blocks.*
   - Write `D = Σ_(s in S) D_s s` with `S` finite and `D_s in M_d(Z)`.
   - For `η in Z[N]^d` and `t in T`, since the `D_s` have integer entries,
     `(η t) D = Σ_s (η D_s) t s`.
   - Write `t s = n_(t,s) t'` with `t' in T` and `n_(t,s) in N`. Then
     `(η t) D = Σ_s (η D_s n_(t,s)) t'`.
   - So for finite `C_0` and `C_1 = {rep(N t s) : t in C_0, s in S}`, `r_D` restricts to a
     left `Z[N]`-linear map `α : P_(C_0) -> P_(C_1)` between finitely generated free left
     `Z[N]`-modules. It is left linear because `r_D` is left `Z[G]`-linear.
3. *Augmentation of the blocks.*
   - `Z ⊗_(Z[N]) P_C = P_C / I_N P_C = ⊕_(t in C) Z^d`, via `ε_C(Σ_t η_t t) = (ε(η_t))_t`.
   - Identify `⊕_(t in C) Z^d` with the span `Z[C N]^d ⊂ Z[G/N]^d` of the cosets
     `tN = Nt`, `t in C`. Then `ε_C = p_N` on `P_C`, because `p_N(η t) = ε(η) · tN`.
   - Hence `ε_(C_1) α = p_N r_D = r_(p_N(D)) p_N = r_(p_N(D)) ε_(C_0)` on `P_(C_0)`.
   - So `id_Z ⊗ α` is the restriction of `r_(p_N(D))` to `Z[C_0 N]^d`. It is injective
     because `p_N(D)` is regular.
4. *Strebel.* By (S), `α` is injective.
5. *Conclusion.* Suppose `0 != ξ in Z[G]^d` with `ξ D = 0`. Choose `C_0` with `ξ in P_(C_0)`.
   Then `α(ξ) = 0` with `ξ != 0`, a contradiction. So `r_D` is injective on `Z[G]^d`, hence
   on `Q[G]^d`. QED.

**Corollary 1.1.** Let `tau` be an injective torus automaton over `G` and `N <| G` locally
indicable. If `D(tau_N)` is regular, then `D(tau)` is regular and `tau` is onto.

*Proof.* `D(tau_N) = p_N(D(tau))` (Lemma 0.1). Apply Theorem 1, then C1. QED.

**Remark 1.2 (`N = G`).** `tau_G` is `tau` on the constants `Fix(G) = T^d`. It is an injective
self-map of a closed `d`-torus, so a homeomorphism by invariance of domain, and
`ε(D) in GL_d(Z)`. This is the periodic-point lemma of
`torus-automata-over-rf-or-domain-groups-are-surjunctive` at `N = G`. So Corollary 1.1 with
`N = G` shows that every locally indicable group is in `𝒞`.

## 2. Locally normal p-kernels reflect invertibility

This is the p-lifting of swarm-0917-w10-w10-gs-break (lemma posted on the live bus, node
`abelian-groups-are-torus-surjunctive`, not in this worktree). It is re-proved here so that
this route is self-contained.

**Definition.** `N <| G` is *locally normal p* (LNP) if every finite subset of `N` lies in a
finite `p`-subgroup `P <= N` that is normal in `G`. Every finite normal `p`-subgroup is LNP.

**Lemma 2.1.** For a finite `p`-group `P`, the augmentation ideal `ω(P)` of `F_p[P]` is
nilpotent.

*Proof.* Induct on `|P|`; `P = 1` is clear.
1. Pick a central `z in P` of order `p`. The kernel of `F_p[P] -> F_p[P/<z>]` is
   `(z-1) F_p[P]`.
2. Since `z - 1` is central and `(z-1)^p = z^p - 1 = 0` in characteristic `p`, we get
   `((z-1)F_p[P])^p = 0`.
3. By induction `ω(P/<z>)^m = 0`, so `ω(P)^m ⊂ (z-1)F_p[P]`, and `ω(P)^(mp) = 0`. QED.

This is also Lemma 2 of the artifact of `torus-degree-regular-on-prime-power-residual-support`.

**Theorem 2.** Let `N <| G` be LNP and `D in M_d(Z[G])`. If `p_N(D)` has a right inverse in
`M_d(Z[G/N])`, then `D` is regular.

*Proof.*
1. *Lift.* Let `p_N(D) E = I`, and lift `E` to `E' in M_d(Z[G])`. Then `D E' - I` has
   entries in `ker p_N`, which is spanned by the `g(n - 1)`, `g in G`, `n in N`.
2. *Localize.* Finitely many `n` occur. They lie in a finite `p`-subgroup `P <= N` normal in
   `G`. So `D E' - I in M_d(Z[G] ω_Z(P))`.
3. *Reduce mod `p`.* Put `J = F_p[G] ω(P)`.
   - Since `g ω(P) g^-1 = ω(P)`, `J` is a two-sided ideal, and `J^k = F_p[G] ω(P)^k`: use
     `x g = g (g^-1 x g)` for `x in ω(P)^k`.
   - By Lemma 2.1, `J^m = 0` for some `m`.
   - So `D̄ Ē' = I + X` with `X in M_d(J)` nilpotent. Hence `D̄` has a right inverse
     `R = Ē' Σ_(i<m) (-X)^i` in `M_d(F_p[G])`.
4. *Kill a kernel vector.* Suppose `0 != ξ in Z[G]^d` with `ξ D = 0`. Divide `ξ` by the
   largest power of `p` dividing all its coefficients. Then `ξ̄ != 0` in `F_p[G]^d`, and
   `ξ̄ = ξ̄ D̄ R = 0`, a contradiction. QED.

**Corollary 2.2.** Let `tau` be an injective torus automaton over `G` and `N <| G` LNP. If
`D(tau_N)` is regular, then `D(tau)` is regular.

*Proof.*
1. `tau_N` is an injective torus automaton over `G/N` with regular degree (Lemma 0.1), so it
   is onto by C1.
2. So `tau_N` is bijective, and `p_N(D) = D(tau_N) in GL_d(Z[G/N])` (Lemma 0.2).
3. Apply Theorem 2. QED.

**Remark 2.3 (why Theorem 2 needs invertibility, and where kernel descent stops).**
- *Invertibility is needed.* For `G = N = Z/2 = <t>` and `D = 1 + t`, `p_N(D) = 2` is regular,
  but `(1 - t) D = 0`.
- *Kernel descent stops at non-prime-power finite subgroups.* Let `N <| G` contain a finite
  subgroup `K` of order divisible by two primes `p != q`, with `s, t in K` of orders `p, q`.
  - Take the Bezout element `D = a P_s + b P_t in Z[K] ⊂ Z[G]`, with `P_x` the sum over
    `<x>` and `ap + bq = 1`.
  - Then `p_N(D) = ε(D) = 1`.
  - But `D` is a zero divisor in `Q[K]`, hence in `Q[G]`
    (`torus-degree-regular-on-prime-power-residual-support`, part (b)).
  - So no purely algebraic statement "`p_N(D)` invertible implies `D` regular" holds for such
    an `N`.
  - Any descent step through a kernel `N` must use the automaton beyond `p_N(D)`, or else
    `N` has only `p`-power finite subgroups (for various `p`).

## 3. Series and residually finite-nilpotent kernels

Call a normal subgroup `N <| G` *descent-admissible over `G`* (DA) if, for every injective
torus automaton `tau` over `G` at every `d`, regularity of `D(tau_N)` implies regularity of
`D(tau)`. So far:
- (DA-LI) every locally indicable `N <| G` is DA (Corollary 1.1);
- (DA-p) every LNP `N <| G` is DA (Corollary 2.2).

**Lemma 3.1 (series).** Let `1 = N_0 <= N_1 <= ... <= N_r = N` be normal subgroups of `G`.
Suppose that for each `i`, `N_i / N_(i-1)` is DA over `G / N_(i-1)`. Then `N` is DA over `G`.

*Proof.* Let `tau` be injective over `G` with `D(tau_N)` regular. We show by downward
induction on `i` that `p_(N_i)(D)` is regular; `i = r` is the hypothesis.
- By Lemma 0.3, `tau_(N_(i-1))` is an injective torus automaton over `G/N_(i-1)`, of degree
  `p_(N_(i-1))(D)`.
- Its restriction to the fixed torus of `N_i/N_(i-1)` has degree `p_(N_i)(D)`, which is
  regular by induction.
- Since `N_i/N_(i-1)` is DA over `G/N_(i-1)`, `p_(N_(i-1))(D)` is regular.

At `i = 0` this says that `D` is regular. QED.

**Theorem 3 (residual descent).** Let `N <| G`, and let `(M_j)` be a family of normal subgroups
of `G` contained in `N` with these properties:
- it is downward directed: for all `j, k` some `M_l <= M_j ∩ M_k`;
- `∩_j M_j = 1`;
- each `N/M_j` is DA over `G/M_j`.

Then `N` is DA over `G`.

*Proof.* Let `tau` be injective with `D(tau_N)` regular, and suppose `0 != ξ in Z[G]^d` with
`ξ D = 0`.
1. *Separate the support.* The set `F = {g h^-1 : g != h in supp ξ} ∩ N` is finite and
   avoids 1. Each element of `F` avoids some `M_j`, so by directedness a single `M = M_l`
   avoids all of `F`. Pairs with `g h^-1 ∉ N` are separated already mod `N ⊃ M`. So `p_M` is
   injective on `supp ξ`, and `p_M(ξ) != 0`.
2. *Regularity mod `M`.* `tau_M` is injective over `G/M`, of degree `p_M(D)`. Its restriction
   to the fixed torus of `N/M` has degree `p_N(D)`, which is regular (Lemma 0.3). Since `N/M`
   is DA over `G/M`, `p_M(D)` is regular.
3. *Contradiction.* But `p_M(ξ) p_M(D) = p_M(ξ D) = 0` with `p_M(ξ) != 0`. QED.

**Corollary 3.2 (finite nilpotent and residually finite-nilpotent kernels).**
- (i) Every finite nilpotent `N <| G` is DA over `G`.
- (ii) Let `N <| G` be finitely generated and residually finite-nilpotent, i.e. every
  `1 != n in N` survives in some finite nilpotent quotient of `N`. Then `N` is DA over `G`.
  Examples: every finitely generated residually finite-`p` group, such as the Grigorchuk
  group, `Z/p ≀ Z`, or a free group.

*Proof.*
- *(i).* `N = P_1 × ... × P_k` is the product of its Sylow subgroups. Each `P_i` is
  characteristic in `N`, hence normal in `G`. Take the series `N_i = P_1 ... P_i`. The factor
  `N_i/N_(i-1) ≅ P_i` is a finite `p_i`-group normal in `G/N_(i-1)`, so it is LNP and DA by
  (DA-p). Apply Lemma 3.1.
- *(ii), the family.* Let `M_j` be the intersection of all normal subgroups `K <| N` of index
  at most `j` with `N/K` nilpotent.
  - There are finitely many such `K`, since `N` is finitely generated. So `N/M_j` embeds in
    a finite product of finite nilpotent groups, and is finite nilpotent.
  - `M_j` is characteristic in `N`, hence normal in `G`.
  - The family decreases in `j`, and `∩ M_j = 1` by hypothesis.
- *(ii), the descent.* By (i) applied over `G/M_j`, each `N/M_j` is DA over `G/M_j`.
  Theorem 3 applies. QED.

**Definition.** Call `N <| G` *elementary-admissible* if it has a finite series
`1 = N_0 <= ... <= N_r = N` of normal subgroups of `G` in which each factor
`N_i/N_(i-1) <| G/N_(i-1)` is one of:
- locally indicable;
- LNP (over `G/N_(i-1)`);
- finite nilpotent;
- finitely generated residually finite-nilpotent.

By Lemma 3.1 and Corollaries 1.1, 2.2 and 3.2, every elementary-admissible `N` is DA.

## 4. Consequences for C2 and torus surjunctivity

**Corollary 4.1 (extension closure).** If `N <| G` is elementary-admissible and `G/N in 𝒞`,
then `G in 𝒞`. In particular `𝒞` is closed under extensions with locally indicable kernel:
`N` LI and `G/N in 𝒞` imply `G in 𝒞`.

*Proof.* Let `tau` be injective over `G`. Then `tau_N` is injective over `G/N in 𝒞`, so
`D(tau_N)` is regular, and `N` is DA. So `D(tau)` is regular, and `tau` is onto by C1. QED.

**Corollary 4.2 (hosts from established nodes of this worktree).** `G in 𝒞`, so `G` is
torus-surjunctive at every `d`, in each of these cases.
- (a) *`G` has an elementary-admissible normal subgroup `N` with `G/N` residually finite.*
  This includes `N` LI, and it includes every virtually LI group. In the virtually LI case,
  take `N` the normal core of a finite-index LI subgroup; LI passes to subgroups.
  - Source for the quotient: `torus-automata-over-rf-or-domain-groups-are-surjunctive`(a).
- (b) *`G` has an elementary-admissible `N` with every finitely generated subgroup of `G/N`
  RPP.* For example `G/N` is torsion-free abelian, `Z(p^inf)`, locally free, or a locally
  finite `p`-group.
  - Source: `torus-degree-regular-on-prime-power-residual-support`(a).
- (c) *`G` is itself elementary-admissible*, that is, `N = G` and `G/N = 1`. Examples: LI
  groups, (finite `p`)-by-LI groups, LI-by-(finite nilpotent) groups, and
  (f.g. residually finite-`p`)-by-LI groups.
  - Source: `𝒞 ∋ 1` by the periodic-point lemma at `N = G`, Remark 1.2.

**New hosts.** The following use only standard facts:
- Brodskii–Howie: torsion-free one-relator groups are LI.
- Bi-orderable groups are LI.
- Mal'cev: finitely generated residually finite groups are Hopfian, and a finitely presented
  LEF group is residually finite.

The hosts:
- **`BS(2,3) × A_5` and `F × A_5`**, with `F` Thompson's group. Both are LI-by-finite
  (Corollary 4.2(a)).
  - They are finitely presented and not residually finite. For `BS(2,3)` this is because it
    is non-Hopfian. For `F` it is because every proper quotient of `F` is abelian. So they
    are not LEF.
  - They have torsion, so they are not LI and not residually LI-amenable.
  - They have no nontrivial finite normal `p`-subgroup: a finite normal subgroup projects to
    a finite normal subgroup of the torsion-free factor, hence lies in `A_5`.
  - So none of the other torus nodes (RF, RPP, LI, RLA, LEF, `p`-lifting, domain at `d = 1`)
    covers them, nor any combination of these by `p`-lifting.
  - Corollary 4.2(a) covers every `L ⋊ Q` with `L` LI and `Q` residually finite. When `L` is
    finitely presented and not residually finite, and `Q` is finite with no nontrivial normal
    `p`-subgroup, the argument above shows that no other node covers `L × Q`.
- **`BS(2,3) × Γ`**, for `Γ` the Grigorchuk group or any residually finite group, and
  `Γ × BS(2,3)` read the other way (Corollary 4.2(a), or (c) via Corollary 3.2(ii)).

**Corollary 4.3 (reduction of counterexamples).** Suppose C2 fails over `G` at dimension `d`,
witnessed by an injective `tau` with singular `D(tau)`.
- (i) For every elementary-admissible `N <| G`, `tau_N` is an injective torus automaton over
  `G/N`, at the same `d`, with singular degree `p_N(D)`. This is the contrapositive of DA.
- (ii) *LI radical.* The union of a chain of LI normal subgroups is LI: a finitely generated
  subgroup lies in one member. By Zorn there is a maximal LI normal subgroup `M <| G`. The
  group `G/M` has no nontrivial LI normal subgroup, since `L/M` LI with `M` LI makes `L` LI:
  a finitely generated `1 != K <= L` maps onto `Z` through `L/M` if `K ⊄ M`, and directly if
  `K ⊂ M`. By (i), C2 fails over `G/M` at dimension `d`. If `G` is finitely generated, so is
  `G/M`.
- (iii) Consequently, **C2 holds for all groups if and only if it holds for all groups with
  no nontrivial locally indicable normal subgroup.** The same holds for torus surjunctivity.
  Such groups have no nontrivial normal subgroup that is free, torsion-free abelian,
  torsion-free nilpotent, or bi-orderable.
  - *Counterexample hosts can therefore be taken without free normal subgroups.* For
    example, a counterexample over a free-by-`Q`, surface-by-`Q` or `Z^n`-by-`Q` group gives
    one over a quotient of `Q`.
- (iv) *`p`-radical.* For a fixed prime `p`, the subgroup `O_p(G)` generated by all LNP
  `p`-subgroups of `G` is LNP, since `PQ` is a finite normal `p`-subgroup when `P` and `Q`
  are. By (i), a counterexample passes to `G/O_p(G)` for each `p` in turn. This is w10's
  reduction. It is not claimed that `G/O_p(G)` has no nontrivial LNP `p`-subgroup.
- (v) *Caveat.* The two reductions cannot be merged into one radical. Alternating them
  gives an ascending chain of normal subgroups, and at a limit stage the union is not
  elementary-admissible (the series must be finite). DA of such unions is open.

## 5. What this does and does not say

- **Decomposition.** C2 splits along any elementary-admissible normal subgroup into C2 for
  `G/N`. The prerequisite "C2 for `G/N`" can fail on its own, and all the difficulty is
  pushed to groups with trivial LI radical, such as simple groups, `Alt_fin(N)`, and
  Higman-type groups with no LI normal subgroup.
- **Where descent stops (Remark 2.3).** No descent through a normal subgroup containing a
  finite subgroup of non-prime-power order can be purely algebraic in `p_N(D)`. The Bezout
  element has `p_N(D) = 1`. So on `Alt_fin(N)`, which is simple and contains `A_5`, every
  kernel-descent argument is dead: the only kernels are `1` and `G`, and `G` carries the
  Bezout witness. A proof there needs topological input beyond `Fix(N)` for normal `N`.
- **Not claimed.** Nothing here touches finite-alphabet surjunctivity, and DA for infinite
  unions of admissible subgroups is open.
