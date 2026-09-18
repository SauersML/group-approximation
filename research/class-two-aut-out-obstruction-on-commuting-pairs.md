---
rg: 2
id: class-two-aut-out-obstruction-on-commuting-pairs
kind: claim
title: On a commuting pair in IA_n, the class-two virtual-section obstruction of Aut(F_n) to Out(F_n) is one rational quadratic equation in two vectors of H
distinct_from:
  aut-out-free-nilpotent-tower-virtually-splits: that is the OPEN claim that every nilpotent level virtually splits; this is a checkable necessary condition at class two, restricted to one commuting pair, and it decides nothing by itself.
  aut-out-free-abelianized-extension-virtually-splits: that is class one, where the obstruction dies on a finite-index subgroup; this is the class-two test on abelian subgroups.
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no novelty claimed).

Notation: `F = F_n`, `H = F/γ_2`, `Λ²H ≅ γ_2/γ_3` via `[x,y] ↦ x∧y`, and
`E_2 = Aut(F)/Inn(γ_3)`. For `α ∈ IA_n` put `t_α(x̄) = [x^{-1}α(x)] ∈ Λ²H`, the
first Johnson homomorphism.

**Setting.** `α, β ∈ IA_n` have commuting images in `Out(F_n)`, so
`αβα^{-1}β^{-1} = ι_w`. Since `[IA, IA]` acts trivially on `F/γ_3`, `w ∈ γ_2`.
Put `ω = [w] ∈ Λ²H`.

**Criterion.** Suppose `E_2 → Out(F_n)` has a section over a finite-index
subgroup. Then there are `y, z ∈ H ⊗ Q` with

    ω + y∧z + t_α(z) − t_β(y) = 0.                              (Q)

Contrapositive: one commuting pair with no rational solution of (Q) shows that
`Aut(F_n) → Out(F_n)` has no virtual section, via item 1 of
`aut-out-free-nilpotent-tower-virtually-splits`.

**Only the traceless parts matter.** Write `t_α = ad_P + T_α` and
`t_β = ad_Q + T_β`, with `ad_P(x) = P∧x` and `T` in the kernel of the contraction
`H^*⊗Λ²H → H`, over `Q`. Then (Q) is equivalent to
`ω_T + y'∧z' + T_α(z') − T_β(y') = 0`, where `y' = y + P`, `z' = z + Q`, and
`ω_T = ω − P∧Q + T_β(P) − T_α(Q)` satisfies `ad(ω_T) = [T_α, T_β]`.
- **Consequence 1.** If both pairs are inner at level one (`T_α = T_β = 0`),
  there is no obstruction.
- **Consequence 2.** If `α, β ∈ A(2)` (trivial on `F/γ_3`), then `w ∈ γ_4`, so
  `ω = 0` and `y = z = 0` solves (Q).
- **Consequence 3.** If lifts commute in `Aut(F_n)`, `ω = 0` and (Q) is solvable.
  So the test can only fire on commuting pairs of `Out(F_n)` whose rank-two
  abelian subgroup does not lift to `Aut(F_n)` even at class two. No such pair is
  exhibited here.

## Proof

1. **Commutator of arbitrary lifts.** Lifts are `α ι_u = ι_{α(u)} α` and
   `β ι_v = ι_{β(v)} β`. A direct expansion gives
   `[αι_u, βι_v] = ι_W` with
   `W = α(u)·αβ(v)·αβ(u)^{-1}·w·β(v)^{-1}`.
2. **Mod γ_3.** For `x ∈ F`, `α(x) ≡ x·t_α(x̄)`, and
   `αβ(x) ≡ x·t_α(x̄)t_β(x̄)`, because IA acts trivially on `γ_2/γ_3`. The central
   terms collect, and `W ≡ [u,v]·w·(t_α(v̄) − t_β(ū))`. So `[αι_u, βι_v]` is
   trivial in `E_2` exactly when `ω + ū∧v̄ + t_α(v̄) − t_β(ū) = 0`.
3. **Powers.** `ι_w` is central in `⟨α, β, Inn(F)⟩` modulo `Inn(γ_3)`. Indeed
   `α(w)w^{-1} ∈ γ_3`, and `[F, γ_2] ⊆ γ_3`. So `[α^a, β^b] ≡ ι_w^{ab}`, and
   `t_{α^a} = a·t_α`. The pair `(α^a, β^b)` therefore gives the equation
   `ab·ω + ū∧v̄ + a·t_α(v̄) − b·t_β(ū) = 0`.
4. **Restriction.** A section over a finite-index `Γ'` is defined at `ᾱ^a` and
   `β̄^b` for some `a, b ≥ 1`, and its values commute. So the equation in item 3
   has an integral solution. Then `(y, z) = (ū/b, v̄/a)` solves (Q) over `Q`.
   Conversely, a rational solution with denominators dividing `d` gives an
   integral solution for `a = b = d`. So over `Q` all the powers are equivalent.
5. **Traceless reduction.** Take the identity `(y+P)∧(z+Q) = y∧z − Q∧y + P∧z + P∧Q`.
   Use `[D, ad_P] = ad_{D(P)}` for derivations to compute
   `ad(ω) = [t_α, t_β] = ad(P∧Q) − ad(T_β(P)) + ad(T_α(Q)) + [T_α, T_β]`.
   The identification `ad(ω) = [t_α, t_β]` is the second Johnson homomorphism of
   the inner automorphism `ι_w`, and `ad: Λ²H → Hom(H, L_3)` is injective for
   `n ≥ 2`. Substituting these gives the traceless form. Consequences 1–3 are
   read off directly.
