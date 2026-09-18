---
rg: 2
id: li-garside-criterion-fails-on-artin-monoid-omega-infinity
kind: claim
title: Li's groupoid of a finite-type Artin monoid on Omega_infinity is the partial action on the positive Deligne boundary, and Li's finiteness hypothesis (t<d) fails there already for B_3
distinct_from:
  garside-decorated-groupoids-hide-artin-groups-in-isotropy: that is about Li's boundary, the single point Δ^∞, where the Artin group sits in isotropy; this is about the larger space Omega_infinity, where the Artin group acts with the correct dynamics but Li's finiteness criterion fails.
  li-finite-k-graph-full-groups-are-f-infinity: that is Li's theorem for finite k-graphs, where (t<d) holds because degrees commute; this records that it fails for Garside monoids.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**ESTABLISHED** (lane proof, not reviewed). This is a record of why a route fails, not a
theorem about finiteness.

**Credit.** Item 1 is standard for quasi-lattice ordered groups: finite-type Artin
groups are quasi-lattice ordered, and the identification of `Ω` with directed
hereditary subsets goes back to Nica and Crisp--Laca. It is included for completeness.
The (t<d) computation in item 2 is a lane observation.

Li's text is arXiv:2110.04505v2, in the gq scratchpad `src/kep/`. The relevant places
are:
- `Ω_∞` (l. 1126);
- the degree-map `𝔛` and `Γ` (l. 1937–1943);
- (St) (l. 1219–1227);
- (t<d) (l. 1611);
- `thm:deg` (l. 2055).

## Setting

- `A` is a finite-type Artin group with at least two atoms, and `C = A^+` is a
  one-object category.
- `C_P` is its binary-decorated version, with degree map `(p, w) ↦ p` into `P = A^+`.
  Its Garside family is `Div(Δ) ∖ 1`.
- `∂A^+` is the space of infinite left-greedy forms, with the product topology.

## Statement

1. **The space and the groupoid.**
   - `Ω_∞(A^+)` is homeomorphic to `∂A^+`.
   - `I_l(A^+) ⋉ Ω_∞` is the partial transformation groupoid of `A` acting on `∂A^+` by
     left multiplication, which is the positive part of the BBCMP action.
   - Li's boundary `∂Ω` is the single point `Δ^∞`.
   - For `C_P`, the space is `Ω_∞ ≅ ∂A^+ × {0,1}^N`.
2. **(t<d) fails.** Take `C = A^+` or `C_P`, `X = Ω_∞`, and let the base object `*` be
   `X` or `Q = X(1; Δ)` (first factor `≠ Δ`). Take any `𝔛`, `Γ` satisfying (St) and
   containing `*`.
   - For `A = B_3`, condition (t<d) fails.
   - So neither `thm:Fn` nor `thm:deg` applies.

## Proof

1. **The space.**
   - Constructible right ideals are principal, since `pA^+ ∩ qA^+ = (p∨q)A^+`.
   - No principal ideal is a finite union of strictly smaller ones, so Li's cover
     condition is vacuous and `Ω` is the set of all characters.
   - Characters correspond to nonempty down-sets `F ⊆ A^+` closed under `∨`.
   - `F` is principal iff it is finite. `Ω_∞` removes the principal ones.
   - For infinite `F`, let `m_k = max(F ∩ Div(Δ^k))`. Then `m_k = m_{k+1} ∧ Δ^k`, and
     `sup(m_k) = k`, since otherwise the chain stops. So `F` is the ideal of the infinite
     form with prefixes `m_k`, and conversely. The topologies match on cylinders.
2. **The groupoid.**
   - Every element of `I_l` is `λ_p λ_q^{-1}`, because `λ_q^{-1}λ_p = λ_{p'}λ_{q'}^{-1}`
     for `p∨q = qp' = pq'`.
   - Two germs at a point agree iff the partial bijections of `A^+` agree on some
     `rA^+`, i.e. iff `pq^{-1} = p'q'^{-1}` in `A`.
   - The maximal character is `F = A^+`, the point `Δ^∞`.
   - The decorated case is the same computation carried out factorwise.
3. **(t<d) fails for B_3.** Use `C_P`; the undecorated case is the same without
   decorations. `Γ` must contain the expansions forced by (1_Γ) and (2_Γ).
   - **A reachable type.** The full expansion `γ(𝔢, 𝔖)` of `*` has the piece
     `(a,u)·X(1; d^{-1}b)` after `(a,u)`, since `min{f : af simple} = {b}`. So
     `X(1; d^{-1}b)` lies in `𝔛(*)`. It consists of the points whose first factor is `a`
     or `ab`.
   - **A forced expansion.** By (2_Γ) with `c = (ab, ·)`, the set
     `𝔰 = {s : ‖cs‖ = 1} = d^{-1}(a)` gives an expansion `γ(d^{-1}b, d^{-1}a) ∈ Γ(*)`.
   - **Its pieces.**
     - `mcm((a,u), (b,u')) = {(Δ, u v') : v' ∈ {0,1}^2}` if `u = u'`, and is empty
       otherwise. So `𝔣_{(a,u)} = d^{-1}(ba)`.
     - The pieces are `(a,0)X(1;d^{-1}ba)` and `(a,1)X(1;d^{-1}ba)`, together with the
       empty piece `X(1; d^{-1}{a,b})`.
   - **Neither piece has the input type.** `X(1; ba)` contains `b^∞`, but `X(1; b)` does
     not.
   - Elements of `𝐂^*` have components `λ_u` with `u ∈ C^* = {1}`, so they only permute
     pieces. Hence no two pieces of `γu` equal the input, and (t<d) fails.
   - For `* = Ω_∞`, the type `X(1; b)` is reached in the same way. ∎

## Reading (lane)

- **Why it fails.** For k-graphs, (t<d) holds because the tail constraint after a
  maximal element keeps its type, since degrees commute. In a Garside monoid the constraint
  "`sw` avoids `e`" becomes "`w` avoids `s^{-1}(s∨e)`", which is a new type.
- **It is the method that fails, not finiteness.** For `B_3` the reduction of this
  groupoid to `Q` is the groupoid of the Deligne shift of finite type. It is
  topologically free by `artin-deligne-boundary-actions-are-topologically-free`, and its
  germs are prefix replacements by `b3-deligne-boundary-is-nonsingular-rank-three-is-not`.
  Its full groups should therefore be Matui groups, which are `F_∞`.
- **The path-category model.** Take vertices = simples and arrows = left-weighted pairs.
  Its `∂Ω` is the same space, with groupoid the shift-of-finite-type groupoid.
  - In rank at least three, `A` does not act by its germs
    (`b3-deligne-boundary-is-nonsingular-rank-three-is-not`, item 2).
  - `λ_y` is not a self-similar action on this graph either, because its letter map is
    not injective. In `B_3`, both `a·a` and `a·ab` output `a` first.
  - So neither Li's k-graph theorem nor his Zappa--Szép theorem places `A` in an `F_∞`
    full group this way. The remaining route is the singular-germ route of
    `automatic-groups-embed-in-corner-germ-extensions`.

## Lesson for general BH

- **(t<d) is a commutativity condition on tail types.** It demands that every
  expansion reproduce its input type. That holds for k-graphs, whose degrees commute,
  and for `∂Ω`, whose types are trivial.
- **Garside monoids offer two losing choices.**
  - Li's boundary collapses to a point, so the group hides in isotropy.
  - `Ω_∞` carries the right dynamics, but its tail types mutate:
    "`sw` avoids `e`" becomes "`w` avoids `s^{-1}(s∨e)`". Then (t<d) fails.
- **What this leaves.** Li's `F_∞` machine cannot be the finiteness engine for
  boundary hosts of non-abelian Garside inputs. The engine has to be a finite germ
  extension (Belk--Hyde--Matucci) over a shift-of-finite-type full group, with the
  input's flats as the singular germ groups.
