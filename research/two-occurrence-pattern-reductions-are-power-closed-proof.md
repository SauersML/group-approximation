---
rg: 2
id: two-occurrence-pattern-reductions-are-power-closed-proof
kind: route
title: "Proof: the empty word fixes R, the pattern becomes a conjugation equation stable under powers, and Bass--Serre theory computes the centralizer of the new central letter"
target: two-occurrence-pattern-reductions-are-power-closed
requires:
  - type-f-group-receives-re-languages-by-pattern-reductions
---

Verification tier: proposed-established. These are elementary paper proofs.
The prerequisite is needed only for the comparison with four occurrences.

## Step 1. Normal form of a two-occurrence pattern

The empty word is in `L`, so `phi(ε) = 1` gives `PQR = 1` in `H`, and
`R = (PQ)^-1`. For `X ∈ H`,

    omega(X) = P X^{e1} Q X^{e2} Q^-1 P^-1 = 1   iff   X^{e1} Q X^{e2} = Q.

## Step 2. Power closure

- **Opposite signs** (`e2 = -e1`). The condition says `X^{e1}` commutes with `Q`, that is `X ∈ C_H(Q)`.
  - `C_H(Q)` is a subgroup, so `L = phi^{-1}(C_H(Q))` is closed under concatenation.
  - In particular `L` is closed under positive powers.
- **Equal signs** (`e2 = e1 = e`). Write `Y = X^e`, so the condition is `Y Q Y = Q`. If it holds, then by induction on `n`
  `Y^n Q Y^n = Y^{n-1} (Y Q Y) Y^{n-1} = Y^{n-1} Q Y^{n-1} = ... = Q`.
  Since `phi(u^n) = phi(u)^n`, `u ∈ L` implies `u^n ∈ L`.
- **Example.** If `ε ∈ L`, `a ∈ L` and `aa ∉ L`, then `L` is the preimage of no word problem under any two-occurrence pattern. `{ε, a}` is such a language. ∎

## Step 3. Coset realization for word problems

- **Setting.** Let `A` be closed under formal inverses, with `a -> a^-1` the involution. For a word `v`, write `v̄` for its formal inverse. Suppose `v =_G 1` iff `phi(v) ∈ C`, for a subgroup `C`.
- **Well defined.** Let `v =_G v'`. Then `v v̄ =_G 1` and `v' v̄ =_G 1`, so `phi(v) phi(v̄) ∈ C` and `phi(v') phi(v̄) ∈ C`. Hence `C phi(v) = C phi(v̄)^-1 = C phi(v')`.
- **Injective.** Let `C phi(v) = C phi(v')`. Then `phi(v) phi(v̄') ∈ C phi(v') phi(v̄') = C`, so `v v̄' =_G 1`, so `v =_G v'`.
- **Equivariant.** `C phi(v) · phi(a) = C phi(va)`.
- **Converse.** Every such realization is a letter-local reduction to membership in `C`. If `C = C_H(Q)`, it is the two-occurrence pattern `X Q X^-1 Q^-1`. ∎

## Step 4. Amalgam realization

Let `H` and `S ≤ H` be of type `F`, and `K = H *_S (S × <q>)`.

- **Type F.** `S × Z` is of type `F`. An amalgamated free product of type `F` groups over a type `F` subgroup is of type `F`: glue the finite `K(π,1)`s along a mapping cylinder of a finite `K(S,1)`. The result is aspherical by Whitehead's theorem on graphs of aspherical spaces with injective edge maps.
- **Setup.** Let `T` be the Bass--Serre tree. Let `u` be the vertex fixed by `B = S × <q>`. The edges at `u` are the cosets `bS`, `b ∈ B`.
- **Fixed set of `q`.** `q` fixes the edge `bS` iff `b^-1 q b ∈ S`. But `q` is central in `B`, so `b^-1 q b = q`, and `q ∉ S`. So `q` fixes no edge at `u`. The fixed set of an elliptic element is a subtree, so it is `{u}`.
- **Centralizer.** If `z` commutes with `q`, then `z` preserves `Fix(q) = {u}`, so `z ∈ Stab(u) = B`. Conversely `B` centralizes `q`. So `C_K(q) = S × <q>`.
- **Intersection with `H`.** `H ∩ B = S` in an amalgam.
- **Conclusion.** For `X ∈ H`, `X q X^-1 q^-1 = 1` in `K` iff `X ∈ S`. So a letter-local reduction `WP(G) = phi^{-1}(S)` becomes a two-occurrence pattern reduction into the type `F` group `K`. ∎

## Step 5. Where the window stands

- **r = 2.**
  - Opposite signs: power closure for arbitrary languages (dead as completeness). For word problems it is equivalent to coset realization. By Step 4 it is implied by letter-local type `F` subgroup membership.
  - Mikhailova gives `WP(G) = phi^{-1}(S)` in `F_2 × F_2` with `phi(a) = (a,1)` and `S = {(u,v) : u =_G v}`. For `G` finitely presented `S` is finitely generated, but it is not of type `F` in general. For an r.e. but not finitely presented `G`, `S` is infinitely generated.
  - Aanderaa--Cohen--Boone realizes halting as `Z^-1 T_0 Z ∈ <t, r_i>`, a type `F` (free) subgroup, but the element carries two copies of `Z`.
  - Equal signs: unsettled beyond power closure.
- **r = 3.** Untouched here. Power closure does not follow from the same computation, since `P X Q X R X^-1 S` does not collapse to one conjugation equation.
