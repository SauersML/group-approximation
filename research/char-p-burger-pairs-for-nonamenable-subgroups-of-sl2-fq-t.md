---
rg: 2
id: char-p-burger-pairs-for-nonamenable-subgroups-of-sl2-fq-t
kind: claim
title: "For every subgroup Λ of SL_2(F_q[t]), the pair (Λ ⋉ F_q[t]², F_q[t]²) has relative property (T) if and only if Λ is non-amenable; so a free linear part already gives a relative-(T) pair with an infinite elementary abelian base"
distinct_from:
  elementary-linear-semidir-pair-relative-t: that needs the whole elementary group EL_2(R); this needs only a non-amenable subgroup, for example a free group of rank two, whose quotient has neither (τ) nor property FM
  char-p-burger-lamp-realizations-refute-haagerup: that is a lifting criterion whose linear part must contain EL_2(F_p[t,t^-1]); this is the relative-(T) input for a much smaller linear part over the polynomial ring F_q[t]
  wobbling-normal-relative-t-subgroups-are-locally-finite: that constrains witnesses inside W(Z); this produces new witnesses whose base is locally finite, as that node requires
---

**ESTABLISHED** by `char-p-burger-pairs-nonamenable-sl2-fq-t-proof`.
- This is a lane proof by swarm-0917-w23-w23-nv-break, and it has not been independently reviewed.
- It is the characteristic-`p` analogue of Burger's theorem for non-amenable `Λ ≤ SL_2(Z)` acting on `Z²`. No priority is claimed: the statement may be covered by Cornulier's work on relative (T) for semidirect products (recalled, not checked).
- The proof imports only two things:
  - textbook facts about the Bruhat–Tits tree of `SL_2(K)`, from Serre, *Trees*, Chapter II, §1 (recalled, not quoted verbatim);
  - the spectral theorem for unitary representations of countable abelian groups.

## Setting

- `q` is a power of a prime `p`, and `R = F_q[t]`. `M = R²` is the module of column vectors, an infinite elementary abelian `p`-group.
- `Λ ≤ SL_2(R)` is any subgroup, and `Γ = Λ ⋉ M` with `(λ, a)(μ, b) = (λμ, a + λb)`.
- More generally, `Δ` is any countable group with a homomorphism `ρ : Δ → SL_2(R)`, and `Γ_ρ = Δ ⋉_ρ M`.
- A pair `(G, H)` has *relative property (T)* if every unitary representation of `G` with almost invariant vectors has a nonzero `H`-invariant vector.

## Statement

1. `(Λ ⋉ M, M)` has relative property (T) if and only if `Λ` is non-amenable.
2. More generally, `(Δ ⋉_ρ M, M)` has relative property (T) whenever `ρ(Δ)` is non-amenable. This holds whether or not `ρ` is injective.
3. **(Free linear part.)** `SL_2(F_q[t])` contains a free subgroup `F` of rank two. For such `F`, the pair `(F ⋉ F_q[t]², F_q[t]²)` has relative (T).
   - `SL_2(F_q[t])` is a lattice in the non-amenable group `SL_2(F_q((1/t)))`, so it is non-amenable.
   - Amenability is a local property, so some finitely generated subgroup of it is non-amenable.
   - By the Tits alternative, that subgroup contains a free group of rank two.

## Role

- **New witness shape for `full-shift-full-group-has-infinite-normal-relative-t-subgroup`.** A copy of `F ⋉ F_q[t]²` inside `[[X]]`, with `F` free (or any non-amenable `Λ ≤ SL_2(F_q[t])`), would refute `full-shift-topological-full-group-is-a-t-menable`, and with it `brin-thompson-groups-nv-are-a-t-menable` for every `n ≥ 2`.
- **It escapes three later class kills.** The quotient `Γ/M = F` is free, so:
  - it fails (τ), since `F` maps onto `Z`, and `Z` onto every `Z/n`, with no uniform gap;
  - it fails Cornulier's property FM, since `F` acts on `Z` through a surjection, with an invariant mean and no finite orbit;
  - it lies in `[[X]]`.

  So the (τ)-quotient and FM-quotient class kills recorded on the live bus in waves 18–21 do not apply. Those kills are `wobbling-tau-subgroups-need-coamenable-infinite-index-subgroup` and `wobbling-relative-t-pairs-with-fm-quotient-are-finite`; they are not yet present in this worktree. Neither does the conditional import of (τ) for `SL_2(F_p[t,t^-1])`.
- **It is strictly weaker than the named candidate.** `F ⋉ F_p[t]² ≤ SL_2(F_p[t]) ⋉ F_p[t]² ≤ Γ_p = EL_2(F_p[t,t^-1]) ⋉ F_p[t,t^-1]²`. So any embedding of `Γ_p` gives one of `F ⋉ F_p[t]²`, and the converse fails.
- **It satisfies the forced shape.** The base `F_q[t]²` is locally finite, as `wobbling-normal-relative-t-subgroups-are-locally-finite` requires.
- **The remaining rank-two obstruction.** The live-bus node `rank-two-affine-relative-t-pairs-in-wobbling-groups-fail-tau` (wave 19, not in this worktree) still applies whenever `F ⋉ F_q[t]²` is *finitely generated*, that is, whenever `F_q[t]²` is a finitely generated `F`-module.
  - That node reduces an embedding to a failure of uniform spectral gap for `F` along its congruence-type finite `F`-sets.
  - This is a super-strong-approximation question for thin subgroups of `SL_2(F_q[t])`: a better-studied statement, and unknown to this lane at all levels in characteristic `p`.
  - The countable version, with `M = F_q[t]²` not finitely generated over `F`, is not reached by that node, which assumes a finite generating set.
