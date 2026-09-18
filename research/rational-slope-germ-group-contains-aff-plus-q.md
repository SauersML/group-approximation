---
rg: 2
id: rational-slope-germ-group-contains-aff-plus-q
kind: claim
title: The rational-slope germ group at infinity contains Aff+(Q) = Q x| Q_{>0}
distinct_from:
  rational-slope-germ-groups-have-bs-but-no-heisenberg: that proves E contains every BS(1,m) and no Heisenberg group; this asks whether all rational dilations and translations fit together in E.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes Aff(Q) from T-bar and Aut(F), where the translations meet a central shift; in E the shift is not central, so that obstruction does not apply.
  gl-n-q-embeds-in-fp-simple-group: that is the target; this is a germ-level stepping stone toward a finite germ extension of V containing Aff(Q).
  commensurating-end-germ-groups-omit-aff-q: that proves no finitely generated subgroup of this E contains Aff_K(Q) for non-finitely-generated K; this asks the same for E itself, which is not finitely generated.
artifacts:
  - research/artifacts/gq-gq-q-in-germs-anatomy.md
---

**OPEN.** Let `E` be the group of germs at `+∞` of `φ ∈ PL₂(R)` with `φ(y+q) = φ(y) + r`
for large `y`, some `q, r ≥ 1`, with slope `λ(φ) = r/q`
(`rational-slope-germ-groups-have-bs-but-no-heisenberg`). Does `E` contain a subgroup
isomorphic to `Aff⁺(Q) = Q ⋊ Q_{>0}`?

**Why it matters.** `E` is the natural enlargement of the slope-one germ group `T̄` of
`VA` (`va-singular-point-germ-groups-are-t-bar`). A yes, together with a Belk–Hyde–Matucci
finiteness check (arXiv:2407.03149 Thm 2.1) for a germ extension of `V` with singular germs
in `E`, would give a finitely presented host for `Aff⁺(Q)`. That host would escape O4 (`E`
has `BS(1,m)`), and would have index 2 in a host for `Aff(Q)`. Lane `gq-va-affq` owns the
global construction.

**Necessary conditions** (lane proofs; not independently reviewed). Suppose
`Aff⁺(Q) ≅ D ⋊ P ≤ E`, where `D ≅ (Q,+)` and `P ≅ Q_{>0}` acts by `a_μ d a_μ^-1 = d^μ`.
1. `D ≤ K = ker λ`, because `D = [D ⋊ P, D ⋊ P]` and `λ` has abelian image.
2. Let `τ` be the translation number on `K`. It is additive on the abelian group `D` and
   satisfies `τ(φ k φ^-1) = λ(φ) τ(k)` (proof of item 3 of the BS/Heisenberg node).
   Then `τ(d) ≠ 0` for every `d ≠ 1` in `D`, and `λ(a_μ) = μ` for every `μ`.
   - `τ|_D: Q → R` is a homomorphism, so either `τ|_D ≡ 0` or `τ(d) ≠ 0` for all
     `d ≠ 1`.
   - All nontrivial elements of `D` have the same support `S`, since
     `supp(g^n) = supp(g)` for increasing maps.
   - Suppose `τ|_D ≡ 0`. Then `S` is periodic and nonempty, with `N ≥ 1` components per
     period, and each `a_μ` maps `S` onto `S` near `+∞`. The component count of that
     proof forces `λ(a_μ) = 1`. So `D ⋊ P ≤ K`, and the finitely generated subgroup
     `BS(1,2) ≤ Aff⁺(Q)` lies in one `C(z^q) ≅ T̄`.
   - That is impossible: `T̄ ≤ VA` has no distorted cyclic subgroup (O4). An elementary
     proof is Lemma D1 of the artifact.
   - Hence `τ(d) ≠ 0`, and `μ τ(d) = τ(d^μ) = λ(a_μ) τ(d)` gives `λ(a_μ) = μ`.
3. No `φ ∈ E` with `λ(φ) ∉ 2^Z` commutes with an affine dilation `y ↦ 2^k y` (`k ≥ 1`).
   - From `φ(2^k y) = 2^k φ(y)` and `φ(y+q) = φ(y) + r` one gets
     `φ(y + q 2^(-kj)) = φ(y) + r 2^(-kj)` for all `j`.
   - So `φ(y) − (r/q)y` is invariant under a dense set of translations, hence constant.
   - Then `φ` is affine with slope `r/q`, which is not a power of 2, so `φ ∉ PL₂(R)`.
   - So in any copy of `Aff⁺(Z[1/6])` in `E`, the dilation of slope 2 is not affine.

**First falsifiable step.** Decide whether `E` contains `Aff⁺(Z[1/6]) = Z[1/6] ⋊ Z²`.
That means commuting `φ_2, φ_3 ∈ E` with `λ = 2, 3` and `u ∈ K` with `φ_m u φ_m^-1 = u^m`.
By condition 3 neither `φ_m` may be affine. A proof of impossibility would kill this
germ-level route to `Aff(Q)`, and with it every host whose singular germs are
rational-slope PL₂ germs.

**Host-level caveat.** In a finite germ extension of `V` satisfying Belk–Hyde–Matucci
Theorem 2.1 with `n ≥ 1`, the germ group at a point `p` is the image of `SingFix({p},{p})`.
That group has type `F_1`, so the germ group is finitely generated and its slopes form a
finitely generated subgroup of `Q_{>0}`. By condition 2, no copy of `Aff⁺(Q)` can then fix
`p` and act faithfully through its germs at `p`. A positive answer here is therefore only
the local ingredient; the global host must spread the dilations over infinitely many points
(artifact §5).

## Attempts

1. **Necessary conditions** (lane `gq-q-in-germs`, 2026-09-17): the three conditions above
   and the host caveat.
2. **Finitely generated subgroups of `E` are settled negatively** (lane `gq-va-affq`,
   780e84702: `commensurating-end-germ-groups-omit-aff-q`). Its `Comm_inf` is this `E`.
   - No finitely generated subgroup of `E` contains `Aff_K(Q)` for any `K <= Q_{>0}`
     that is not finitely generated. That covers `Aff⁺(Q)`, `SL_2(Q)` and `PSL_2(Q)`.
   - The mechanism is `aff-q-forces-distortion-in-abelian-kernels`: a distorted pair lands
     in `ker λ`, whose finitely generated subgroups lie in one `C(z^q) ≅ T-bar`.
   - This agrees with conditions 1–2 here: they force `λ(E_0) ⊇ K` for any finitely
     generated `E_0` containing the copy.
3. **Every periodic-point germ host is settled negatively** (lane `gq-va-affq`, ff94a5e66:
   `periodic-point-germ-groups-omit-aff-q`). A finite germ extension of any `V_{d,r}` has,
   at finitely many eventually periodic points, finitely generated germ groups that
   commensurate the local contraction. Their product contains no `Aff_K(Q)`.
   - So an affirmative answer to this node can no longer feed a Belk–Hyde–Matucci host
     whose relevant germs sit at finitely many periodic points.
   - What remains open is only the germ-level question for the non-finitely-generated `E`
     itself. A host would need infinitely many germ orbits or germs at non-periodic
     points.
