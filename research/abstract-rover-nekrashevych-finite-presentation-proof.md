---
rg: 2
id: abstract-rover-nekrashevych-finite-presentation-proof
kind: route
title: Place labels on cones by V_d-conjugation, expand them by the recursion relation, and invert the presentation map with a table-to-word map
target: abstract-rover-nekrashevych-groups-are-finitely-presented
requires: []
---

Notation as in the target. `Π` is the group given by the presentation in the target, and
`Ξ : Π → V_d(G, ψ)` sends `v ∈ V_d` to itself and `x_s` to the class of "`s` on `C(1)`".

**Inputs.** Higman (1974): `V_d = V_(d,1)` is finitely presented and `V_(d,r)` is finitely
generated.

## 0. Facts about V_d

- A nonempty clopen `Y ⊆ C_d` is a disjoint union of `m` cones exactly for the `m ≥ m_0(Y)`
  with `m ≡ c(Y) mod (d − 1)`, for a residue `c(Y)`: splitting a cone adds `d − 1`.
- `c(C_d) = 1` and `c(C(w)) = 1`.
- If `Y, Y'` are proper nonempty clopens with `c(Y) = c(Y')`, then any cone partitions of `Y` and
  `Y'` of equal size, together with equal-size cone partitions of the complements, define an
  element of `V_d` that maps `Y` onto `Y'` by prefix replacement on the chosen cones.

Consequences, for nonempty words:
- for every `w ≠ ∅` some `a ∈ V_d` has `a(1u) = wu` for all `u` (the complements have residue
  `0`);
- for incomparable `w, w'` with `C(w) ∪ C(w') ≠ C_d`, some `b ∈ V_d` has `b(wu) = 11u` and
  `b(w'u) = 12u` (the complements have residue `−1` and are nonempty; `C(2)` misses
  `C(11) ∪ C(12)`).

## 1. The relations hold in V_d(G, ψ)

- **(R_V).** `V_d` is the subgroup of label-1 tables, since `ψ(1)` is trivial.
- **(R_1), (R_2).** The factors have disjoint supports as tables.
- **(R_3).** Conjugating by `c_i` moves "`g` on `C(1)`" to "`g` on `C(1i)`". The right side
  is then the table `1i ↦ 1π_s(i)` with labels `s_i`, which is the expansion at `1` of
  "`s` on `C(1)`".
- **(R_4).** `g ↦` "`g` on `C(1)`" is a homomorphism `G → V_d(G, ψ)`.

So `Ξ` is well defined. It is onto, because every table is a label-1 table times labels on
cones, and "`g` on `C(w)`" is a `V_d`-conjugate of "`g` on `C(1)`".

## 2. Four lemmas in Π

`ι_1 : G → Π`, `g ↦ ĝ(x)`, is a well-defined homomorphism by (R_4).

**L1 (labels on cones).** For `w ≠ ∅` put `ι_w(g) = a ι_1(g) a^{−1}` for any `a ∈ V_d` with
`a(1u) = wu`. Two such `a` differ by an element of `Fix_1`, which commutes with `ι_1(G)` by
(R_1). So `ι_w` is a well-defined homomorphism.

**L2 (transport).** If `v ∈ V_d` has `v(wu) = w'u` for all `u`, then
`v ι_w(g) v^{−1} = ι_{w'}(g)`, because `va` is admissible for `w'`.

**L3 (disjoint cones commute).** Let `w, w'` be incomparable, nonempty, with
`C(w) ∪ C(w') ≠ C_d`.
- Conjugate by the `b` of §0.
- `c_1` and `c_2` are admissible for `11` and `12`.
- So the claim is `[c_1 ι_1(g) c_1^{−1}, c_2 ι_1(h) c_2^{−1}] = 1`. That holds for
  generators by (R_2), hence for all `g, h`.

**L4 (expansion).** For `w ≠ ∅` define `Φ_w : S_d ≀_d G → Π` by
`Φ_w(π⟨g_1, ..., g_d⟩) = (π at w) · ∏_i ι_{wi}(g_i)`,
where `(π at w) ∈ V_d` acts by `wiu ↦ wπ(i)u` on `C(w)` and is the identity elsewhere.
- **The factors commute** by L3: the cones `wi` are pairwise incomparable, and their union
  `C(w) ≠ C_d`.
- **Φ_w is a homomorphism.** By L2, `(ρ at w)^{−1} ι_{wj}(f) (ρ at w) = ι_{wρ^{−1}(j)}(f)`,
  so `∏_j ι_{wj}(f_j) · (ρ at w) = (ρ at w) · ∏_i ι_{wi}(f_{ρ(i)})`. Hence
  `Φ_w(π⟨f⟩) Φ_w(ρ⟨h⟩) = (πρ at w) ∏_i ι_{wi}(f_{ρ(i)} h_i) = Φ_w(π⟨f⟩ · ρ⟨h⟩)`.
- **The claim: `ι_w = Φ_w ∘ ψ`.** Both sides are homomorphisms `G → Π`. On a generator `s`,
  conjugate (R_3) by an admissible `a` for `w`:
  - `a e_s a^{−1} = (π_s at w)`;
  - `a c_i` is admissible for `wi`.

**L3′ (the missing case).** If `d = 2`, then `ι_1(g)` and `ι_2(h)` commute. Expand
`ι_1(g) = (π_g at 1) ι_{11}(g_1) ι_{12}(g_2)` by L4.
- `(π_g at 1)` fixes `C(2)` pointwise, so it commutes with `ι_2(h)` by L2.
- The pairs `(11, 2)` and `(12, 2)` fall under L3.

So `ι_p(g)` and `ι_q(h)` commute for every pair of distinct cones `p, q` of any cone
partition other than `{∅}`.

## 3. The inverse map Θ : V_d(G, ψ) → Π

Take a table `τ = (P, Q, β, λ)` with `∅ ∉ P`. Let `v_β ∈ V_d` be the element with
`v_β(pu) = β(p)u`, and put
`θ(τ) = v_β · ∏_{p ∈ P} ι_p(λ(p))`,
in any order (L3, L3′).

**(i) Invariance under expansion.** Expand at `p`, with `λ(p) = g` and `ψ(g) = π⟨g_i⟩`.
- The new permutation element is `v_β (π at p)`.
- The new labels are `g_i` on `pi`.
- By L4, `ι_p(g) = (π at p) ∏_i ι_{pi}(g_i)`.
- `(π at p)` commutes with `ι_q` for `q ∈ P \ {p}`, by L2.
- So `θ(τ^{(p)}) = θ(τ)`.

**(ii) Well defined on classes.** Equivalent tables have a common expansion, and every class
has a representative with `∅ ∉ P`. So `θ` induces a map `Θ` on `V_d(G, ψ)`.

**(iii) Homomorphism.** Represent two classes by `τ = (R, Q, β, λ)` and
`τ' = (P', R, β', λ')`. Then:
- by L2, since `v_{β'}^{−1}` maps `β'(p)` onto `p` prefixwise:
  `∏_{r ∈ R} ι_r(λ(r)) · v_{β'} = v_{β'} · ∏_{p ∈ P'} ι_p(λ(β'(p)))`;
- so `θ(τ)θ(τ') = v_β v_{β'} · ∏_p ι_p(λ(β'(p)) λ'(p)) = θ(ττ')`.

**(iv) Two-sided inverse.**
- `Ξ(θ(τ)) = τ`, since `Ξ` sends `ι_p(g)` to "`g` on `C(p)`".
- `Θ(Ξ(v)) = v` for `v ∈ V_d`: a label-1 table gives `v_β = v`.
- `Θ(Ξ(x_s)) = ι_1(s) = x_s`.

So `Θ ∘ Ξ` is a homomorphism that is the identity on generators, hence the identity, and
`Ξ` is an isomorphism. The presentation has finitely many generators, and finitely many
relations when `R` is finite. ∎

## Where faithfulness would have entered, and does not

- Classes are defined by expansion alone, never by the action on `C_d`.
- `V_d → V_d(G, ψ)` is injective because the composite to `Homeo(C_d)` is the standard
  faithful `V_d`. Only label-1 tables are involved there.

So nothing uses the kernel of `ρ_ψ`. It survives in `V_d(G, ψ)` as `K_ψ` (target, Setting).
