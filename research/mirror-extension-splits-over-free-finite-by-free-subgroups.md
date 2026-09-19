---
rg: 2
id: mirror-extension-splits-over-free-finite-by-free-subgroups
kind: claim
title: The mirror extension 1 -> [T_-] -> N_- -> SL_n(A) -> 1 splits over every commuting pair (x_12(a), h^k) and over every virtually free subgroup whose finite subgroups lift, because lifts of a finite group that agree modulo the full group of the ergodic tail relation are conjugate by it, so the Fredholm obstruction to virtual splitting has no measurable shadow
distinct_from:
  jacobson-symbol-sequence-does-not-virtually-split: that proves no lifts of u_a = x_12(a) and h^k commute in E = EL_n(J), where the kernel is the finitary group L; this proves that commuting lifts do exist once the kernel is enlarged to the full group [T_-] of the tail relation, so that node's obstruction does not pass to (HS).
  mirror-lift-untwists-only-through-a-mirror-splitting: that reduces the canonical bilateral route to (SR) and (HS) and proposes deciding (HS) on the commuting pair (u_a, h^k) through a relative-entropy index; this decides that test (the pair splits) and extends it to every finitely generated virtually free subgroup with liftable finite subgroups, so the index route and every test of that shape are dead.
  finite-subgroups-of-full-cantor-groups-conjugacy-criterion: that is a conjugacy criterion for finite subgroups of topological full groups of Cantor systems; this is the measurable statement for finite groups of automorphisms normalizing an ergodic p.m.p. relation and agreeing modulo its full group, with the conjugator required inside the full group [T], not inside a full group containing the action.
  outer-covering-lifts-are-virtual-sections: that is a general equivalence between lifting outer classes and virtual sections of Aut -> Out; this is a specific splitting theorem over virtually free subgroups for the measurable mirror extension, proved by conjugacy of finite lifts.
artifacts:
  - research/mirror-extension-splits-over-free-finite-by-free-subgroups-proof.md
---

**ESTABLISHED** (route `mirror-extension-splits-over-free-finite-by-free-subgroups-proof`,
swarm-0917-w16-w16-nh-follow, 2026-09-19, unreviewed). Role: belief-breaker, decomposition lane of
`non-hyperlinear-group`. It decides, positively, the next falsifiable step named on
`mirror-lift-untwists-only-through-a-mirror-splitting`.

**Setup.** The notation is that of `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift`, with `n >= 3`.
* `X_- = Hom(V_-, F_2)` has Haar measure `mu_-`. `T_-` is its tail relation: `x ~ y` iff `x - y` is finitely supported.
* `N_- = Ê_- [T_-]`, with `pi_- : N_- -> Q = SL_n(A)` and `A = F_2[x, x^(-1)]`. The sequence
  `1 -> [T_-] -> N_- -> Q -> 1` is exact.
* **(HS) over a group `Λ`.** For a homomorphism `rho : Λ -> Q`, the statement is: there is a homomorphism
  `rho~ : Λ -> N_-` with `pi_- o rho~ = rho`.
  (HS) of the node above is the case `Λ = Q`, `rho = id`.

**Theorem.**
1. **(Conjugacy of finite lifts; abstract.)** Let `T` be an ergodic p.m.p. countable Borel equivalence relation on a
   standard probability space `(X, mu)`. Let `F` be a finite group, and let `alpha', alpha'' : F -> N[T]` be
   homomorphisms such that:
   * `alpha'` and `alpha''` both act essentially freely;
   * `alpha'(f)^(-1) alpha''(f) ∈ [T]` for every `f`.

   Then there is `s ∈ [T]` with `alpha''(f) = s alpha'(f) s^(-1)` for every `f ∈ F`.
2. **(Freeness is automatic.)** Let `F <= Q` be finite. Every homomorphism `alpha : F -> N_-` with
   `pi_- o alpha = id_F` acts essentially freely on `X_-`.
3. **(Splitting over virtually free groups.)** Let `Λ` be the fundamental group of a finite graph of finite groups
   `(G_v, G_e)`. Let `rho : Λ -> Q` be injective on each vertex group, and suppose each restriction `rho|G_v` lifts to a
   homomorphism `G_v -> N_-`. Then `rho` lifts to a homomorphism `Λ -> N_-`.

   In particular, (HS) holds over every finitely generated virtually free subgroup `Λ <= Q` whose finite subgroups all
   lift to `N_-`. The special cases are:
   * `F x| Λ_0` with `F` finite and liftable and `Λ_0` free;
   * amalgams and HNN extensions of liftable finite groups.
4. **(The named test.)** For every `a ∈ A \ {0}`, every `k ∈ Z` and every `h ∈ Q` commuting with `u_a = x_12(a)`,
   there are a measure-preserving involution `u' ∈ u~[T_-]` and an automorphism `h' ∈ h~[T_-]` with `u' h' = h' u'`.
   Here `u~ = x_12(a~)` is the elementary lift and `h~` is any lift.
   * This applies in particular to `h = diag(x, x, x^(-2), 1, ..., 1)^k` of
     `jacobson-symbol-sequence-does-not-virtually-split`.
   * More generally, the same holds for `x_12(W)` with `W ⊂ A` any finite additive subgroup, and for every constant
     subgroup `SL_n(F_2)`, together with any free subgroup of their normalizer.
   * These finite groups lift through `Ê_-` by additive Toeplitz lifts and by constant block matrices.
5. **(Locally finite subgroups; finite Steinberg shadow.)** Let `Λ <= Q` be an increasing union of finite subgroups
   that each lift. Then `Λ` lifts. The proof extends lifts exactly along the chain by the conjugacy of part 1, so no
   limit is taken.
   * The order-`2^7` group `<x_12(1), x_12(x), x_23(1), x_23(x^(-1))> <= UT_3(A)` lifts even into `Ê_-`, with
     `x_23(1)` lifted as `x_23(pq)`.
   * Every lift of a subgroup of `Q` is properly outer modulo `[T_-]`.

**What this kills (class kill, named invariant, death step).**

*Class.* Every attempt to refute (HS), and hence under (SR) to refute (ML) and the canonical bilateral lift, through
a subgroup of `Q` of the form "finite ⋊ free", or more generally a virtually free subgroup with liftable finite
subgroups. This includes:
* the relative-entropy index `H(h'F | F) - H(F | h'F)` of the `u'`-invariant σ-algebra (Section 5 of
  `mirror-lift-untwists-only-through-a-mirror-splitting-proof`);
* any measurable image-layer or Fredholm-type index attached to a commuting pair `(u', h')`.

*Invariant.* These obstructions are functions of the pair of `[T_-]`-cosets alone, and `[T_-]` acts transitively on
the free lifts of a finite group inside those cosets (part 1).

*Death step.* For a commuting pair such an index has to take the same value at a genuinely commuting pair, which
exists by part 4. So it cannot certify non-splitting.

The linear obstruction of `jacobson-symbol-sequence-does-not-virtually-split` dies exactly at the replacement of
`L_-` by `[T_-]`: the conjugator `s` of part 1 sends a fundamental domain of `u'` onto one of `h~ u' h~^(-1)`. It has
unbounded displacement, which is precisely the regime flagged as the failure point of the entropy index.

**What survives.** (HS) over `Q` is still OPEN. Any refutation must use a subgroup that is not virtually free, or a
finite subgroup of `Q` that does not lift to `N_-`. Candidates:
* a rank-2 free abelian subgroup such as the diagonal pair `diag(x, x^(-1), 1)`, `diag(1, x, x^(-1))`. There,
  (HS) asks whether the centralizer `C_(N_-)(g)` of one lift maps onto `C_Q(pi_-(g))`. Equivalently, it asks whether
  `g` and `g t`, for `t` in a prescribed class of `[T_-]`, are `[T_-]`-conjugate, which is an exact-coboundary
  (not approximate) Rokhlin question;
* a Steinberg-type relation among infinite-order elements. The finite Steinberg test does lift, even linearly;
  see the proof, Section 5;
* the Kazhdan subgroups themselves.

**Next falsifiable steps** (proof, Section 6).
* **(FL)** Does every finite subgroup of `Q` lift to `N_-`? One that does not lift refutes (HS).
* **(Z2)** The diagonal torus test above. Its obstruction would have to be a `[T_-]`-outer-conjugacy invariant that
  is not `N[T_-]`-invariant.
* **(AM)** `T_-` is hyperfinite, and the lifts are properly outer. So Ocneanu-type 2-cocycle vanishing for `[T_-]`-valued
  cocycle actions of amenable groups would give (HS) over every amenable subgroup of `Q`, including (FL) and (Z2).
  That would leave only the Kazhdan part. It is not proved here.

Proof: [[mirror-extension-splits-over-free-finite-by-free-subgroups-proof]].
