---
rg: 2
id: abelian-lamp-wreaths-are-rf-iff-stabilizers-are-closed
kind: claim
title: A permutational wreath product with nontrivial abelian lamps is residually finite exactly when lamps and acting group are residually finite and every point stabilizer is profinitely closed
distinct_from:
  z-wr-psl2-z-half-is-not-residually-finite: that is the instance with a profinitely dense stabilizer, answering arXiv:2609.01868 Question 1.1; this is the general criterion, both directions.
  kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers: that uses the fibre-summing map inside a soficity argument for finite lamps; this states the residual-finiteness criterion itself for arbitrary abelian lamps.
  wreath-subgroups-meeting-lamps-finitely-are-rf: that gives residual finiteness of subgroups meeting the lamp kernel finitely; this characterizes when the whole wreath product is residually finite.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No priority is claimed: this is
the permutational form of Gruenberg's criterion and is very likely folklore.

## Statement

Let `G` be a group, `X` a `G`-set with orbits `G/K_j` (`j ∈ J`), and `A ≠ 1` an abelian
group. Put `W = A ≀_X G = A^(X) ⋊ G`. Then `W` is residually finite if and only if

1. `A` and `G` are residually finite, and
2. every point stabilizer `K_j` is closed in the profinite topology of `G`, i.e.
   `K_j = ⋂ {K_j N : N ⊴ G, [G:N] < ∞}`.

## Proof

**Necessity of 1.** `A` and `G` are subgroups of `W`.

**Necessity of 2.** Suppose `g ∈ \bar K ∖ K` for a stabilizer `K = Stab(o)`. Let
`ψ: W -> Q` be a homomorphism to a finite group, and `N = ker(ψ|_G)`. Since
`g ∈ KN`, write `g = λ n` with `λ ∈ K`, `n ∈ N`. For `a ∈ A ∖ {1}` and `a_x` the lamp
`a` at `x`,

    ψ(a_{go}) = ψ(g a_o g^{-1}) = ψ(λ) ψ(n a_o n^{-1}) ψ(λ)^{-1} = ψ(λ a_o λ^{-1}) = ψ(a_o),

because `ψ(n) = 1` and `λ o = o`. Since `g ∉ K`, `go ≠ o`, so `a_o (a_{go})^{-1} ≠ 1`, yet it
dies in every finite quotient.

**Sufficiency.** Let `w = (f, g) ≠ 1`.
- If `g ≠ 1`, a finite quotient of `G`, composed with `W -> G`, detects `w`.
- If `g = 1`, the support of `f` is a finite set `x_1, …, x_k` of distinct points.
  - For `x_i = g_i K_j`, `x_l = g_l K_j` in the same orbit, `g_l^{-1} g_i ∉ K_j = \bar K_j`.
    So some finite-index normal `N_{il}` has `g_l^{-1} g_i ∉ K_j N_{il}`. Let `N` be the
    intersection of these finitely many subgroups, over all pairs in the same orbit.
  - Then `π: X -> Y = ⊔_j G/K_j N`, `x ↦ xN`, is `G`-equivariant and injective on
    `{x_1, …, x_k}`, and each orbit of `Y` is finite.
  - Let `Y'` be the finite union of the `G`-orbits of `Y` containing some `π(x_i)`. Pushing
    lamps forward, `f ↦ π_* f` (sum over fibres; a homomorphism because `A` is abelian),
    gives `Φ: W -> A ≀_{Y'} G`, killing lamps outside `π^{-1}(Y')`. `Φ(w) = (π_* f, 1)`,
    and `π_* f(π(x_i)) = f(x_i) ≠ 0` by injectivity.
  - `A ≀_{Y'} G = A^{Y'} ⋊ G` with `Y'` finite contains `A^{Y'} × N'` with finite index,
    where `N'` is the kernel of `G -> Sym(Y')`. That subgroup is residually finite, since
    `A` and `N'` are, so `A ≀_{Y'} G` is too, and it detects `Φ(w) ≠ 1`.

## Lesson for general BH

Residual finiteness of a permutational wreath product sees exactly one extra thing about
the stabilizer: profinite closure. Decidability of membership, which is what Boone–Higman
needs (`pbh-closed-under-decidable-permutational-wreaths`), is logically independent of it.
So:
- **RF-host routes cover only closed stabilizers.** Self-similar groups, automaton groups,
  and the whole Zaremsky "f.p. self-similar ⇒ f.p. simple" route are residually finite. They
  can host `A ≀_{G/K} G` only when `K` is profinitely closed, e.g. every f.g. `K` in a LERF
  `G` (free groups, surface groups).
- **Non-LERF inputs force other hosts.** With `K` dense, as for `PSL_2(Z) ≤ PSL_2(Z[1/n])`
  (congruence subgroup property), the input needs a non-residually-finite host. The
  clopen-stabilizer mechanism of `wreaths-over-clopen-stabilizer-cosets-lie-in-b-a` works
  exactly because clopen stabilizers in `V`-type hosts need not be profinitely closed.
- **A quick test before designing a host for any permutational wreath or coset-HNN
  input.** Compute the profinite closure of the stabilizer. If it is larger, discard every
  residually finite host class at once.
