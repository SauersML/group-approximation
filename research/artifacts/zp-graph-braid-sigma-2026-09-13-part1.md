# BNSR invariants of graph braid groups, part 1: setup and the Euler-characteristic obstruction

Lane z1-08-graph-braid, 2026-09-13. Root: `zaremsky-1-08-bnsr-invariants-of-graph-braid-groups`.

## 1. Setup

`Γ` is a finite connected graph, `n ≥ 1`, and `UConf_nΓ` is the space of
`n`-element subsets of `Γ`. `B_nΓ = π_1(UConf_nΓ)`.

Abrams' discretized configuration space `UD_nΓ` is the cube complex whose
cells are the sets `{c_1,…,c_n}` of closed cells of `Γ` (vertices and edges)
with pairwise disjoint closures. A cell with `k` edge entries is a `k`-cube.
It is nonpositively curved. If `Γ` is sufficiently subdivided, `UD_nΓ` is a
deformation retract of `UConf_nΓ`: Abrams (PhD thesis, Berkeley, 2000); the
subdivision hypotheses were improved by Kim–Ko–Park (arXiv:0805.0082,
Trans. AMS) and by Prue–Scrimshaw. Farley–Sabalka (arXiv:math/0410539,
AGT 5 (2005)) show that `UConf_nΓ` strong deformation retracts onto a CW
complex of dimension at most the number `k(Γ)` of vertices of degree `≥ 3`.

Consequences used below:

- `B_nΓ` is of type F;
- `cd B_nΓ ≤ min(n, k(Γ))`;
- the Euler characteristic `e(B_nΓ) = e(UD_nΓ)` equals
  `Σ_j (−1)^j c_j(Γ,n)`, where `c_j(Γ,n)` counts the cells of `UD_nΓ` with
  exactly `j` edge entries, computed on any sufficiently subdivided `Γ`.

A closed form is attributed to Ś. Gal (Colloq. Math. 89 (2001)):
`Σ_n e(UConf_nΓ) t^n = Π_{v∈V(Γ)} (1 + (1 − deg v) t) / (1 − t)^{|E(Γ)|}`.
The source statement is still to be checked. I checked the formula against
direct computation for the interval (`e = 1` for all `n`), the circle
(`e = 0` for `n ≥ 1`) and the triod (`e_1 = 1`, `e_2 = 0`, and indeed
`UConf_2` of the triod is homotopy equivalent to a circle).

Characters and the sphere: `S(G) = (Hom(G,ℝ) \ 0)/ℝ_{>0}`. `Σ^m(G)` is the
homotopical and `Σ^m(G;ℤ)` the homological BNSR invariant, with
`Σ^m(G) ⊆ Σ^m(G;ℤ)` and `Σ^{m+1} ⊆ Σ^m`.

## 2. Theorem E (Euler-characteristic obstruction)

**Theorem E.** Let `G` be a group of type F with Euler characteristic
`e(G) ≠ 0`, and let `d ≥ cd G`, `d ≥ 1`. Then
`Σ^d(G;ℤ) ∩ −Σ^d(G;ℤ) = ∅`. Hence `Σ^m(G) ∩ −Σ^m(G) = ∅` for every
`m ≥ d`.

**Proof.**

1. (Bieri–Renz, Comment. Math. Helv. 63 (1988).) Each `Σ^m(G;ℤ)` is open in
   `S(G)`. For a character `χ` with `χ(G) = ℤ`, the kernel `ker χ` is of type
   `FP_m` if and only if both `[χ]` and `[−χ]` lie in `Σ^m(G;ℤ)`.
2. Suppose `U = Σ^d(G;ℤ) ∩ −Σ^d(G;ℤ)` is nonempty. It is open, since the
   antipodal map is a homeomorphism of `S(G)`. Classes of rational
   characters (`χ(G) ⊆ ℚ`) are dense in `S(G)`, because `H^1(G;ℚ)` is a
   ℚ-structure on `H^1(G;ℝ) = Hom(G,ℝ)`. Pick one in `U` and rescale it so
   that `χ(G) = ℤ`.
3. By step 1, `N = ker χ` is of type `FP_d`. Also `cd N ≤ cd G ≤ d`. A group
   of cohomological dimension `≤ d` that is of type `FP_d` is of type FP
   (Brown, *Cohomology of Groups*, VIII.6.1).
4. `1 → N → G → ℤ → 1` is an extension of groups of type FP. So the Euler
   characteristic is multiplicative: `e(G) = e(N)·e(ℤ) = 0` (Brown, IX.7.3).
   This contradicts `e(G) ≠ 0`.
5. `Σ^m(G) ⊆ Σ^m(G;ℤ) ⊆ Σ^d(G;ℤ)` for `m ≥ d`. ∎

The argument is a standard combination of the cited results. Its content
here is the application below.

## 3. Corollary for graph braid groups

**Corollary E1.** Let `k(Γ)` be the number of vertices of degree `≥ 3`, and
let `d = max(1, min(n, k(Γ)))`. If `e(UD_nΓ) ≠ 0`, then no character class
of `B_nΓ` lies in both `Σ^d(B_nΓ)` and `−Σ^d(B_nΓ)`. In particular:

- no map `B_nΓ → ℤ` has a kernel of type FP;
- every character `χ` with `[χ], [−χ] ∈ Σ^m(B_nΓ)` for `m ≥ d` is excluded.

So when `e ≠ 0` the invariants `Σ^m` for `m ≥ d` contain no antipodal pair.

**Calibration.**

- `n = 1`: `B_1Γ = F_r` with `r = 1 − e(Γ)`. For `r ≥ 2`, `e ≠ 0`,
  consistent with `Σ¹(F_r) = ∅`. For `r = 1`, `e = 0` and `Σ¹ = S⁰`.
- Triod, `n = 2`: `e = 0`, `B_2 = ℤ`, `Σ^∞ = S⁰`, the symmetric case, as the
  theorem allows.
- `Γ = K_5` or `K_{3,3}`, `n = 2` (next section): `e = −5`, resp. `−3`,
  `d = 2`, and indeed `Σ¹ = ∅`.

## 4. Two surface cases

`UD_2K_5`: 10 vertices, 30 edges, 15 squares, so `e = −5`. The link of a
vertex `{u,v}` has as vertices the moves `u→w`, `v→w` with `w ∉ {u,v}`
(3 + 3 moves). Two moves span a link edge iff they move different particles
to different targets. So the link is a 6-cycle, and `UD_2K_5` is a closed
surface with `e = −5`, i.e. nonorientable of genus 7.

`UD_2K_{3,3}`: 15 vertices, 36 edges, 18 squares, so `e = −3`. The link of
`{a,a'}` (same side) is a 6-cycle. The link of `{a,b}` (opposite sides) is
`K_{2,2}`, a 4-cycle. So `UD_2K_{3,3}` is a closed nonorientable surface of
genus 5.

(Abrams's thesis states the ordered versions `D_2K_5`, `D_2K_{3,3}` as
orientable surfaces of genus 6 and 4. The unordered complexes are their free
`ℤ/2` quotients; the Euler characteristics halve, matching the counts.)

For `n = 2` the subdivision hypothesis holds for `K_5` and `K_{3,3}` without
subdividing: every cycle has length `≥ 3`. So `B_2K_5 ≅ π_1(N_7)` and
`B_2K_{3,3} ≅ π_1(N_5)`.

A nontrivial finitely generated normal subgroup of infinite index cannot
exist in the fundamental group of a closed surface with negative Euler
characteristic. Pass to the orientable double cover; the classical theorem
is due to Griffiths (1967), and the source statement is still to be checked.
The kernel of a nonzero character is normal, nontrivial and of infinite
index. So `Σ¹(B_2K_5) = Σ¹(B_2K_{3,3}) = ∅`, and hence every `Σ^m` is empty.
