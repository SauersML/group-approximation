---
rg: 2
id: subshift-group-factor-supports-are-relative-commutants
kind: claim
title: In L(G_X), the subalgebras of subgroups supported on complementary clopen sets are mutual relative commutants, and GL_3(LC(X,F_2)) generates an irreducible hyperfinite subfactor
distinct_from:
  subshift-elementary-group-rigid-supports-are-mutual-centralizers: that computes centralizers inside the group G_X; this computes relative commutants inside the von Neumann algebra L(G_X), which contain non-group elements and need the finite-conjugacy-class analysis of LC(U,GL_3(F_2)).
  subshift-group-unitary-embeddings-are-corner-subfactors: that concerns embeddings of G_X into unitary groups of other algebras; this describes subalgebras of the single factor L(G_X) coming from support subgroups.
artifacts:
  - research/artifacts/subshift-group-factor-support-commutants-2026-09-16.md
---

**Setting.** This is the setting of `subshift-elementary-group-rigid-supports-are-mutual-centralizers`:
- `X` is an infinite minimal subshift, `A = LC(X,F_2)`, `R = A ⋊_T Z` and `G = G_X = EL_3(R)`;
- `L = GL_3(A) = LC(X, GL_3(F_2))`;
- for clopen `U`, `G_U = G ∩ (I + M_3(e_U R e_U))` and `L_U = {l ∈ L : l ≡ I off U}`.

Let `M = L(G)`. For a subgroup `S ≤ G` write `L(S) = λ(S)'' ⊆ M`, and put `N_U = L(G_U)`.

For all clopen `U, V ⊆ X`:
1. `L(L_U)' ∩ M = N_(X∖U)`.
2. `N_U' ∩ M = N_(X∖U)`, so `N_U` equals its relative bicommutant `(N_U' ∩ M)' ∩ M`.
3. The support subalgebras behave like a Boolean algebra:
   - `N_U ∩ N_V = N_(U∩V)` and `(N_U ∨ N_V)' ∩ M = N_(X∖(U∪V))`;
   - `U ↦ N_U` is injective;
   - for `U ≠ ∅`, `N_U` is a II_1 factor, so `G_U` is ICC.
4. `N_U ∨ N_(X∖U) ≅ N_U ⊗̄ N_(X∖U)`, with trivial relative commutant in `M`.
5. `L(L)' ∩ M = C`, and `L(L)` is the weak closure of an increasing union of finite-dimensional *-subalgebras. So
   `L(G_X)` contains `L(GL_3(LC(X,F_2)))` as an irreducible hyperfinite II_1 subfactor.
6. **Transport.** Let `θ: L(G_X) → L(G_Y)` be a *-isomorphism with `θ(L(L^X_U)) = L(L^Y_(U'))`. Then
   `θ(N^X_U) = N^Y_(U')` and `θ(N^X_(X∖U)) = N^Y_(Y∖U')`.

**Scope.**
- This describes the pair `(L(G_X), λ(G_X))`, not an invariant of the factor.
- Nothing here says that an arbitrary isomorphism `L(G_X) ≅ L(G_Y)` carries some `L(L^X_U)` to an algebra of the form
  `L(L^Y_(U'))`.
- That missing hypothesis of item 6 is where the von Neumann version of diagonal recognition stops. See
  `notes/subshift-group-factors-determine-subshif-swarm-2026-09-16.md`.

Proof: route `subshift-group-factor-support-commutants-proof` (unreviewed), full argument in the artifact.

**Referee (swarm landing, 2026-09-16): PASS.** Every step of artifact §1–§6 was re-derived. This includes the
finite-index core argument (Lemma 3.1), both sides of the intersection lemma (Lemma 4.1) under the convention
`u f u^(-1) = f∘T^(-1)` of the rigid-supports artifact, and the edge cases `U = ∅` and `U = X`. No gap was found. Details
are in the notes file above, section Referee. The argument is textbook Fourier analysis combined with two reviewed
graph claims, and no novelty is claimed.
