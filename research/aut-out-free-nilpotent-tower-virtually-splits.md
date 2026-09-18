---
rg: 2
id: aut-out-free-nilpotent-tower-virtually-splits
kind: claim
title: Every nilpotent quotient of the extension of Out(F_n) by its inner automorphisms splits over a finite-index subgroup
distinct_from:
  aut-out-free-abelianized-extension-virtually-splits: that is the class-one case of this claim, established; this is the statement for every nilpotency class.
  aut-free-to-out-free-does-not-virtually-split-in-even-rank: that asserts Aut(F_n) to Out(F_n) has no virtual section in even rank; a failure of this claim at any single class would prove that in every rank at least three, while this claim holding says nothing either way about the full extension.
  out-free-groups-virtually-embed-in-aut-free-groups: that asks for an embedding of a finite-index subgroup of Out(F_n) in some Aut(F_m); this is a filtration of the virtual-section route to it, by finite nilpotent levels.
---

**OPEN** for `n ≥ 3` and `c ≥ 2`. Class `c = 1` is
`aut-out-free-abelianized-extension-virtually-splits`. For `n = 2` every level
virtually splits, because `Out(F_2)` is virtually free.

Let `F = F_n`, `γ_c` its lower central series, `L_c = γ_c/γ_{c+1}` (so
`L_1 = H` and `L_2 ≅ Λ²H`), and

    E_c = Aut(F)/Inn(γ_{c+1}F),   1 → F/γ_{c+1} → E_c → Out(F) → 1.

`Inn(γ_{c+1})` is normal because `γ_{c+1}` is characteristic, and
`Inn(F) ≅ F` because `Z(F) = 1`.

**Claim.** For every `n ≥ 3` and `c ≥ 1`, `E_c → Out(F_n)` has a section over
some finite-index subgroup.

## Elementary reductions (lane proof, not reviewed)

1. **Why a failure would matter.** A section of `Aut(F) → Out(F)` over `Γ`,
   composed with `Aut(F) → E_c`, is a section of `E_c` over `Γ`. So if the claim
   fails for some `(n, c)`, then `Aut(F_n) → Out(F_n)` has no virtual section.
   That kills every lifting construction of
   `out-free-groups-virtually-embed-in-aut-free-groups` in rank `n`, including
   odd rank, which `aut-free-to-out-free-does-not-virtually-split-in-even-rank`
   does not reach.
2. **Why success would not suffice.** Compatible sections at every level only
   give a section into `lim E_c`, an extension of `Out(F)` by `lim F/γ_c`, which
   is strictly larger than `F`. So the claim is a necessary condition only.
3. **Layer obstruction.** Given a section `σ` of `E_c` over `Γ`, its preimage in
   `E_{c+1}` is an extension of `Γ` by the abelian group `L_{c+1}`, with `Γ`
   acting through `GL_n(Z)`. It has a class `o(σ) ∈ H²(Γ; L_{c+1})`, and `σ` lifts
   exactly when `o(σ) = 0`.
4. **The first open level, made explicit.** Let `K_n` be the zero set of
   `k = h/(n − 1)` from the class-one node, so that `K_n ∩ Inn(F) = Inn(γ_2)`.
   Then `P_n = K_n/Inn(γ_3)` is an extension
   `1 → Λ²H → P_n → Γ_n → 1`. Every section of `E_1` over a finite-index
   `Γ' ≤ Γ_n` is the section `σ_0 = K_n/Inn(γ_2)` twisted by a crossed
   homomorphism `z: Γ' → H`. So class 2 virtually splits exactly when, for some
   finite-index `Γ'` and some `z`, `o(σ_0 z) = 0` in `H²(Γ'; Λ²H)`. For `z = 0`
   this is the question whether `P_n` splits over a finite-index subgroup.

## A candidate construction (idea, not proved)

A splitting of `P_n` over `Γ'` is a crossed homomorphism
`k_2: K_n' → Λ²H` with `k_2(ι_g) = [g] ∈ γ_2/γ_3` for `g ∈ γ_2`. The class-one
splitting came from the contraction of the Fox Jacobian, which is the degree-one
Magnus-expansion crossed homomorphism. The natural class-two candidate is a
contraction to `Λ²H` of the degree-two Magnus-expansion map (Kawazumi,
arXiv:math/0505497, not read at source here). Restricted to `K_n`, where the
degree-one contraction vanishes, it may become a crossed homomorphism whose value
on `ι_g`, `g ∈ γ_2`, is a nonzero multiple `m_2·[g]`. If so, dividing by `m_2` on
a finite-index subgroup settles class 2, by the class-one argument. Neither the
crossed-homomorphism property on `K_n` nor the value `m_2` is computed.

**Heuristic contrast with surfaces.** Chen--Salter's surface obstruction is an
Euler-class computation that uses the invariant symplectic form in `Λ²H`.
`GL_n(Z)` fixes no nonzero vector of `Λ²H`, so a free-group obstruction at class 2,
if there is one, cannot come from the same invariant.

## Attempts

1. **Abelian subgroups (09-18).** `class-two-aut-out-obstruction-on-commuting-pairs`:
   on a commuting pair in `IA_n`, class-two virtual splitting forces a rational
   solution of one quadratic equation. Only the traceless Johnson parts matter.
   Pairs that are inner at level one, lie in `A(2)`, or lift to commuting
   automorphisms never obstruct. No obstructing pair is known. If every rank-two
   abelian subgroup of `IA_n` virtually lifts to `Aut(F_n)`, which this lane has
   not checked against Feighn--Handel, the test is empty, and an obstruction must
   be global, as in Chen--Salter.
2. **The abelian test is empty; the global rational class (09-18).**
   - **Attempt 1's test is empty.** By
     `abelian-subgroups-of-out-free-virtually-lift-to-aut` (Feighn--Handel), every
     abelian subgroup virtually lifts to `Aut(F_n)`.
   - **Stable twisted cohomology.** Randal-Williams, arXiv:1604.01701, read from
     its TeX on MSI:
     - Theorem B(ii) and Corollary (i) give `H¹(Out(F_n); H_Q) = 0` for `n ≥ 7` and
       `H²(Out(F_n); Λ²H_Q) ≅ Q` for `n ≥ 11`. The latter corresponds to the
       partition `{2}`.
     - His Proposition in "An integral calculation for Out(F_n)" gives
       `H²(Out(F_n); H) ≅ Z/(n−1)` for `n ≥ 9`, holding unconditionally as he notes.
       It is generated by the class of the abelianized extension, which
       Bridson--Vogtmann (Theorem B) proved nontrivial for all `n ≥ 2`, and
       nontrivial mod `r` for `r` not coprime to `n − 1`. So class one splits
       virtually but never globally.
   - **A well-defined rational invariant (lane, elementary given these inputs).**
     For `n ≥ 11`:
     - the rationalized abelianized extension splits over `Out(F_n)`, because its
       class is torsion;
     - the section is unique up to `H_Q`-conjugacy, because `H¹ = 0`;
     - so the obstruction to lifting it to the rationalized `E_2` is a
       well-defined `o_Q ∈ H²(Out(F_n); Λ²H_Q) ≅ Q`.
   - **Why `o_Q ≠ 0` alone would not decide the claim.** On a finite-index `Γ'`,
     restriction keeps `o_Q` nonzero, by transfer. But a section may be twisted by
     `z ∈ Z¹(Γ'; H_Q)`, which changes the obstruction by a linear-plus-quadratic
     term. Randal-Williams controls `H¹` only for `Out(F_n)` itself. So killing
     virtual sections needs two inputs:
     - (a) `o_Q ≠ 0`;
     - (b) a virtual vanishing statement, e.g. `H¹(Γ'; H_Q) = 0` for all
       finite-index `Γ'`, or control of the twist term.

     Neither is decided here. The candidate for computing `o_Q`: its pullback to
     `Aut(F_n)`, where `H²(Aut; Λ²H_Q) ≅ Q²` for `n ≥ 7`. There the pullback is the
     twist of the tautological section by the Fox cocycle `k`, which gives
     `[k∪k]` plus the evaluation of Kawazumi's first Magnus cocycle on `k`, and
     injectivity of `π^*` (`aut-out-free-abelianized-extension-splits-rationally`)
     reduces `o_Q ≠ 0` to that class being nonzero.
