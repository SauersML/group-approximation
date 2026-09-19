---
rg: 2
id: soluble-minimax-radicals-are-twisted-by-s-units
kind: claim
title: In a finitely generated soluble minimax group every element acts on the rational Tate module of the finite residual with eigenvalues that are products of at most c eigenvalues on the torsion-free abelianization of the Fitting subgroup, hence S-units of a number field, and the Fitting subgroup acts unipotently
distinct_from:
  partial-torus-abels-quotients-are-isolated: that builds isolated hosts whose Pruefer corner is twisted by S-units times unipotents over O_K; this proves that every finitely generated soluble minimax group twists its Pruefer radical by S-units on the semisimple side, which is the necessary condition for such hosts to be universal.
  fg-soluble-minimax-groups-can-have-unsolvable-word-problem: that shows the data by which the radical is reached can be transcendental or non-computable; this shows the eigenvalues of the twist never are.
  compact-skew-products-cannot-carry-divisible-fiber-subgroups: that is a host obstruction for the divisible centre; this is a structure theorem for the action on the divisible radical.
---

**ESTABLISHED** (lane `bh-solvable`, lane proof from cited structure theory; not independently
reviewed; no priority claimed, and the statement may well be folklore). This answers question (a)
of the coordinator's isolated-host program positively on the semisimple side.

## Imports

- Kropholler–Lorensen, *Virtually torsion-free covers of minimax groups*, arXiv:1510.07583v3,
  Proposition 1.3 (read in the PDF; they cite Lennox–Robinson, *The Theory of Infinite Soluble
  Groups*, 2004, for proofs): for a virtually soluble minimax group `G`, "(i) Fitt(G) is nilpotent
  and G/Fitt(G) virtually abelian", "(iii) R(G) is a direct product of finitely many quasicyclic
  groups", "(iv) G is a member of 𝔐_1 if and only if R(G) = 1". Here `R(G)` is the finite residual,
  and p. 3 of the same paper: "an 𝔐-group belongs to 𝔐_1 if and only if it is residually finite".
- P. Hall (1959): finitely generated metabelian groups are residually finite (standard, not re-read).

## Statement

Let `G` be a finitely generated soluble minimax group, `F = Fitt(G)` of class `c`, and
`D = R(G)` its finite residual (its Prüfer radical). For a prime `p`, let
`V_p(D) = Hom(Z[1/p]/Z, D) ⊗ Q_p`. Let `A = (F/F')/τ(F/F')` and `A_Q = A ⊗ Q`.

1. `τ(F/F')` is finite, so `A` is torsion-free abelian minimax, and `G` acts on `A_Q` through a
   subgroup of `GL_r(Z[1/n])` for some `n`.
2. For every `g ∈ G`, every eigenvalue of `g` on `V_p(D)` is a product `λ_1 ⋯ λ_i`, `1 <= i <= c`,
   of eigenvalues of `g` on `A_Q`. So it is an `S`-unit of a number field, `S` the primes dividing `n`,
   and a unit at the primes above `p`.
3. `F` acts unipotently on `V_p(D)`. A finite-index subgroup of `G` acts through a unipotent-by-abelian
   group, whose abelian quotient acts on the graded pieces of a `G`-stable filtration by commuting
   matrices with `S`-unit eigenvalues.

## Proof

1. **No Prüfer part in F/F'.** Take `G_0 ≤ G` of finite index containing `F` with `G_0/F` abelian
   (Prop. 1.3(i)). Then `G_0/F'` is finitely generated metabelian, hence residually finite, and so is
   `G/F'`. A quasicyclic subgroup of `F/F'` lies in the finite residual of `G/F'`, which is trivial.
   So `τ(F/F')` is a minimax torsion abelian group without divisible part, hence finite. `A` is
   torsion-free minimax, so after choosing `Z^r ⊆ A` of full rank, `A ⊆ (1/n)Z[1/n]^r` for some `n`,
   and `A[1/n] = Z[1/n]^r` is `G`-stable. So `G → GL_r(Z[1/n])`, whose eigenvalues are `S`-units.
2. **D sits in F.** `D` is abelian and normal, so `D ≤ F`. The subgroups `D_i = D ∩ γ_i(F)` are
   `G`-invariant, and `D_(c+1) = 1`.
3. **Tate modules.** `T_p = Hom(Z[1/p]/Z, −)` is left exact, so the graded pieces of the
   filtration `V_p(D_i)` embed `G`-equivariantly in `V_p(τ(γ_i/γ_(i+1)))`, `γ_i = γ_i(F)`.
4. **Commutator maps.** Iterated commutators give a `G`-equivariant surjection
   `B_i = (F/F')^(⊗i) → γ_i/γ_(i+1)`. By step 1, `τ(B_i)` is finite, and `B_i/τ(B_i)` is
   torsion-free of finite rank with `(B_i/τ(B_i)) ⊗ Q = A_Q^(⊗i)`.
5. **Divisible torsion of a quotient.** Let `B` be torsion-free of finite rank with a `G`-action and
   `K ≤ B` a `G`-invariant subgroup, with isolator `K̄`, so that `τ(B/K) = K̄/K`. The snake lemma for
   multiplication by `p^m` on `0 → K → K̄ → K̄/K → 0` gives
   `(K̄/K)[p^m] ≅ ker(K/p^mK → K̄/p^mK̄)`, naturally and compatibly in `m`. So
   `T_p(K̄/K) = ker(K̂_p → K̄̂_p)`, a `G`-submodule of the `p`-adic completion `K̂_p`, which is a
   `G`-quotient of `K ⊗ Z_p`. Hence the eigenvalues on `V_p(K̄/K)` are eigenvalues on `K ⊗ Q`,
   which is a `G`-submodule of `B ⊗ Q`. Finite torsion in `B` changes nothing, since `V_p` kills
   finite groups.
6. Apply step 5 to `B_i/τ(B_i) → (γ_i/γ_(i+1))/(image of τ(B_i))`. The eigenvalues of `g` on
   `A_Q^(⊗i)` are the products `λ_1 ⋯ λ_i`. With steps 2–3 this gives item 2.
7. **Item 3.** `F` is nilpotent and contains `D`, so it acts trivially on every graded piece of the
   filtration of step 2, i.e. unipotently. `G_0/F` is abelian, so `G_0` acts on each graded piece
   through commuting matrices, and the kernel of the action on all graded pieces is unipotent. The eigenvalues are
   given by item 2. ∎

## Calibrations

- **Hall's `B/C`.** `A_Q = Q^2` with `t` acting by `(p^{-1}, p)`, `c = 2`, and `t` acts on `D` by the
  product `1`.
- **bh-free-60's `G_2`.** `t` acts on `D` by `2 = 2 · 1`, a product of eigenvalues on `A_Q`.
- **Split extensions are impossible** for a non-algebraic twist: a module `D ⊕ M` with `t` acting by
  `u` on `D` and by `λ` on a torsion-free `M` splits over `Z[t^±]` whenever `u − λ` is invertible on
  `D`. Non-split reach needs matching eigenvalues, which is the content of item 2.

## What it leaves open

The eigenvalues are algebraic. The maps by which `D` is reached from torsion-free sections are
`p`-adic data, and they can be transcendental, or even non-computable
(`fg-soluble-minimax-groups-can-have-unsolvable-word-problem`). Whether the unipotent part of the
twist itself can be transcendental is not decided here.

## Lesson for general BH

In soluble minimax groups the source of non-residual-finiteness, the Prüfer radical, is always
"reached from above": it lies in the Fitting subgroup, and its Tate module is a filtered
subquotient of `p`-adic completions of tensor powers of a rational `S`-integral module.
- So the eigenvalues of every host-relevant twist are algebraic `S`-units: the torus part of any
  host can be taken arithmetic.
- The only non-arithmetic freedom is `p`-adic linking data, and that is exactly where computability,
  and hence Boone–Higman, enters.
