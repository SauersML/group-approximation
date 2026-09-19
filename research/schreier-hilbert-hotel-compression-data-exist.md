---
rg: 2
id: schreier-hilbert-hotel-compression-data-exist
kind: claim
title: Some finitely generated group has an automorphism, an invariant approximable coset space and a compressed subgroup with a finite image orbit outside the image of the base orbit
refuted_by: [finite-actions-kill-schreier-hilbert-hotel-data, automorphic-compressions-have-no-approximable-hilbert-hotel]
distinct_from:
  schreier-hilbert-hotel-data-give-matricial-compression-rings: that proves (HH) implies R1-R5; this asks whether (HH) data exist at all.
  matricial-compression-ring-exists: that is the ring gate; this is a strictly combinatorial sufficient condition for it, stated for permutation groups.
  rf-hosts-cannot-realize-the-lysenok-substitution: that forbids residually finite hosts of the Lysenok substitution; here it is used to kill the one known local witness, because (HH) forces the host Gamma x|_alpha Z to be residually finite.
  fw-inputs-pass-window-zero-only-via-proper-self-embeddings: that concerns near actions on N twisted by a shift for Boone-Higman shells; this concerns a genuine automorphism of an approximable coset space with a fixed base point and a compressed subgroup.
  automorphism-twisted-shell-actions-have-finitely-many-orbits: that constrains orbit counts of shell actions twisted by the shift; here the twisting map t is an honest bijection of X fixing x_0, and the constraint is on one finite orbit of the compressed image.
---

**OPEN.** There exist data (HH) as in `schreier-hilbert-hotel-data-give-matricial-compression-rings`:

- a finitely generated `Gamma` with `alpha in Aut(Gamma)`;
- an `alpha`-invariant `H <= Gamma` that is a Chabauty limit of finite-index subgroups, such that every
  `gamma != 1` moves infinitely many points of `X = Gamma/H`;
- a finitely generated `Gamma_0 <= Gamma` with `A = alpha(Gamma_0) <= Gamma_0`;
- some `g in Gamma_0` such that `g x_0` has a finite `A`-orbit and `g x_0 notin A x_0`, where `x_0 = H`.

**Why it matters.** By route `matricial-compression-ring-via-schreier-hilbert-hotel`, this implies
`matricial-compression-ring-exists`. Through `xmf-via-matricial-compression-ring-proof` it then gives
`(XMF)` of `mf-kazhdan-quotientless-mapping-torus-exact-radical`. Its kernel is `Q = EL_4(R)`, which is
LEF, so this would also refute `exact-kazhdan-radical-kernel-cannot-be-lef`.

**Local form.** Put `X_0 = Gamma_0 x_0`. The site map `t(gamma H) = alpha(gamma) H` restricts to a
bijection `X_0 -> A x_0` which intertwines `Gamma_0` with `A` through `alpha`. So (HH) asks for a
Schreier graph of `Gamma_0` that contains a copy of itself, relabelled by `alpha`, inside a proper
subset. In the complement of that copy there must be a finite orbit of the relabelled group: a Hilbert
hotel whose complement holds a finite room block.

**Forced necessary conditions** (proved in `schreier-hilbert-hotel-ring-reduction-proof`,
Steps 8-9, and in the Attempts below):

- `X_0` is infinite, and `A` is a proper subgroup of `Gamma_0`.
- `Gamma` and `Gamma x|_alpha Z` are residually finite.
- The action of `Gamma x|_alpha Z` on `X` is not a Chabauty limit of finite actions.

## Attempts

1. **Normal images and finite-index images (2026-09-18, swarm-0917-w13-w13-titz-break, dead class).**
   - *Invariant.* `N = Core_(Gamma_0)(A)`, the largest normal subgroup of `Gamma_0` inside `A`.
   - *Death step.* Suppose `N x_0` is infinite. Then `N g x_0 = g (g^(-1) N g) x_0 = g N x_0` is
     infinite, while `N g x_0 <= A g x_0` must be finite. So (HH) fails.
   - *Why `X_0` is infinite.* If `X_0` were finite, then `t(X_0) = A x_0 <= X_0` would be a
     subset of the same size, hence all of `X_0`, contradicting `g x_0 notin A x_0`.
   - *Casualties.* Everything with `N` of finite index in `Gamma_0` dies, since finitely many
     `N`-orbits then cover the infinite `X_0`. This covers `A` of finite index in `Gamma_0`, `A`
     normal in `Gamma_0` (so abelian `Gamma_0`), and `A >= [Gamma_0, Gamma_0]`. Examples are the
     finite-index self-embeddings of `BS(1,n)`, of lamplighters and of other self-similar groups of
     finite index.
   - *Survivors.* `A` has infinite index and `N x_0` is finite.
2. **Noetherian hosts (dead class).**
   - *Invariant.* The ascending chain `Gamma_0 < alpha^(-1)(Gamma_0) < alpha^(-2)(Gamma_0) < ...`.
     Applying `alpha^(-n)` to the proper inclusion `A < Gamma_0` shows that it is strictly ascending.
   - *Death step.* The chain consists of pairwise isomorphic finitely generated subgroups of `Gamma`.
     - If `Gamma` satisfies the maximal condition on subgroups, the chain stabilizes, a
       contradiction. This kills every polycyclic-by-finite `Gamma`.
     - If `Gamma` is free, Takahasi's theorem stabilizes every ascending chain of subgroups of
       bounded rank. This kills every free `Gamma`.
3. **Small stabilizers (dead class).** If `H` is finite, then `A meet gHg^(-1)` is finite and of
   finite index in `A`. So `A`, and with it `Gamma_0`, is finite, and `X_0` is finite, which
   contradicts item 1. Regular and free actions die.
4. **Inner twists fixing the base point (dead class).** Suppose `alpha = Ad(tau)` with `tau in H`.
   - Then `t(gamma H) = tau gamma H`, so the extended action factors through the map
     `Gamma x|_alpha Z -> Gamma`, `(gamma, m) -> gamma tau^m`.
   - Pulling back `H_n` gives finite-index subgroups converging to `H x| <t>`, which contradicts
     necessary condition (N2).
   - This is Attempt 1 of `matricial-compression-ring-exists`, seen in the coset space.
5. **The Grigorchuk-Lysenok Hilbert hotel (local form realized; every completion dead).**
   - *The local witness.*
     - Let `G` be the first Grigorchuk group with `b = (a,c)`, `c = (a,d)`, `d = (1,b)`, and let
       `sigma : a -> aca, b -> d, c -> b, d -> c` be the Lysenok substitution.
     - Then `sigma(g) = (h(g), g)` on the two level-one subtrees, where `h : G -> <a,d>`
       (dihedral of order 8) is a homomorphism.
     - With `t(w) = 1w` on the boundary and `x_0 = 1^infinity`, we get
       `t(g x) = sigma(g) t(x)`, and `t` fixes `x_0`.
     - Every point `0w` has a `sigma(G)`-orbit of size at most 8, while `sigma(G) x_0` stays inside
       `1{0,1}^N`. Take `g = a`: then `a x_0 = 0 1^infinity`.
     - So the local form of (HH) holds with `Gamma_0 = G` and `X_0 = G x_0`. The only thing missing
       is a finitely generated `Gamma` with an **automorphism** `alpha` extending `sigma`, and an
       approximable `X`.
   - *Where every completion dies.* By necessary condition (N1), `Gamma x|_alpha Z` is residually
     finite, and it contains `G` together with `t` realizing `sigma`.
     - By part 1 of `rf-hosts-cannot-realize-the-lysenok-substitution`, `<G, t>` is then
       `G*_sigma = G~`.
     - `G~` is Grigorchuk's finitely presented group, which is not residually finite (Sapir-Wise, as
       cited there; alternatively `rf-hosts-cannot-realize-branch-substitutions`).
     - This is a contradiction for **every** host `Gamma`, whether `alpha` is inner or outer.
   - *Powers die too.* `sigma^m` gives `<G, t^m>`, which contains the whole normal closure
     `union_n t^(-mn) G t^(mn)` of `G` in `G~`. So it has index `m` in `G~` and is not residually
     finite either.
   - *General form.* If `Gamma` contains a torsion subgroup `P` with `alpha(P) < P` properly, then
     `P *_(alpha|P)` must be residually finite. So torsion branch compressions are excluded wholesale,
     modulo the non-residual-finiteness input for their HNN extensions.
6. **What survives (open gate).** A witness needs all of the following:
   - a finitely generated, residually finite `Gamma` without the maximal condition;
   - an automorphism compressing a finitely generated `Gamma_0` onto an infinite-index `A` whose
     `Gamma_0`-core has finite orbit at `x_0`;
   - no torsion subgroup compressed as in item 5;
   - an extended action on `X` that is not approximable.

   *Candidate to test next.* `Gamma = Z wr_(Z[1/2]) BS(1,2)`, generated by a lamp `a` at `0`, the
   translation `s` and the doubling `tau`. Take `Gamma_0 = <a,s> = Z wr Z` and `alpha = Ad(tau)`, so
   `alpha(s) = s^2` and `alpha(a) = a`. Then:
   - `A` has infinite index in `Gamma_0` and `Core_(Gamma_0)(A) = 1`. A normal subgroup inside `A`
     meets the base `Z[s^(+-1)]` in an `s`-invariant subgroup of the even-supported lamps, which is
     `0`. It then commutes with the base, which is self-centralizing in `Z wr Z`, so it lies in the base
     and is trivial. Item 1 is therefore evaded.
   - The maximal condition fails, so item 2 is evaded. `Gamma` is torsion-free, so item 5 is
     evaded.
   - By item 4, `H` must be normalized by `tau` without containing it.

   Whether such an `H` gives a finite `A`-orbit off `A x_0` is **open**.
7. **Periodicity of precomposition on finite actions (2026-09-19, swarm-0917-w14-w14-titz-follow,
   REFUTED in general).**
   - *Invariant.* For a finite set `F`, the permutation `rho -> rho o alpha` of the finite set
     `Hom(Gamma, Sym(F))` has finite order `k`. With `alpha^k(Gamma_0) <= A <= Gamma_0` this forces
     `rho(A) = rho(Gamma_0)` on every finite `Gamma`-set.
   - *Death step.* The finite orbit `A g x_0` is copied exactly into a finite approximant `Gamma/H_n`.
     There it is an `A`-orbit, hence a `Gamma_0`-orbit, so it contains the base point. Injectivity on
     the ball gives `x_0 in A g x_0`, contradicting `g notin A H`.
   - *Casualties.* Every instance of (HH), for every host, including the candidate
     `Z wr_(Z[1/2]) BS(1,2)` of item 6 and the ascending HNN candidate
     `<a, b, tau | [tau, a], tau b tau^(-1) = b^2>` with `alpha = Ad(tau)`. The item 6 list of
     "what survives" is empty.
   - Proof: `finite-actions-kill-schreier-hilbert-hotel-data`.
7. **Profinite density of automorphic compressions (2026-09-19, swarm-0917-w14-w14-titz-follow,
   refutation).** This claim is **false**. See `automorphic-compressions-have-no-approximable-hilbert-hotel`,
   proved in `automorphic-compression-orbit-rigidity-proof`.
   - *Invariant.* The closure of `Gamma_0` in the profinite completion of `Gamma`.
     - `alpha` permutes the characteristic finite-index subgroups `K_m`. So in each `Gamma/K_m`, the
       image of `A = alpha(Gamma_0)` has the size of the image of `Gamma_0` and is contained in it.
       Hence the two images are equal.
     - It follows that `A N = Gamma_0 N` for every finite-index normal `N`.
   - *Death step.*
     - Transport the finite room block `A g x_0` into an approximant `Gamma/H_n` by the local embedding
       of Step 7 of the reduction proof.
     - There `A` and `Gamma_0` induce the same permutations, so the image block is `Gamma_0`-invariant.
     - Pulling back, `A g x_0` is `Gamma_0`-invariant and contains `x_0`, so `g in A H`.
   - *What it needs.* Only finite generation of `Gamma` and `Gamma_0`, the automorphism, and
     Chabauty approximability of `H`. The `alpha`-invariance of `H`, (IS) and profinite closedness
     are not needed.
   - *Casualties.*
     - Every host, including the item-6 candidate `Z wr_(Z[1/2]) BS(1,2)`. There, (PE) is the fact
       that `s` has odd order in every finite quotient of `BS(1,2)`.
     - The whole Bernoulli tensor-lamp template for `matricial-compression-ring-exists`, by the
       Corollary of the refuting node: `R_0` generated by site algebras and `u_(Gamma_0)`, with the
       root in the lamp algebra, never meets (R5).
   - *Consistency with item 5.* The Grigorchuk-Lysenok local witness uses an endomorphism, not an
     automorphism, and `sigma(G)` has smaller level images than `G`.
