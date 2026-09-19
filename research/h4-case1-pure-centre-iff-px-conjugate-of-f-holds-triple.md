---
rg: 2
id: h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple
kind: claim
title: A single-edge H_4 hexagon has a pure ŝ_4 upper bound iff one P_X-conjugate of F contains its three corner elements; a hexagon vertex is one iff the witness is 1, β_1 or β_3^{-1}
distinct_from:
  h4-case1-pure-normal-form-and-fibred-obstruction: that gives the tuple normal form and the arrangement obstruction; this turns the pure-bound condition for those tuples into a membership problem for the P_X-conjugates of F, decided exactly by the retraction ρ_X.
---

**Setting.** Notation is as in `h4-case1-pure-normal-form-and-fibred-obstruction`.
- `X = {s_2,s_3,s_4}`, `Y = {s_1,s_2,s_3}`, `Z = X ∩ Y`.
- `ρ_X : P → P_X` is the parabolic retraction. It is a homomorphism and the identity on `P_X`.
- `F = ker(ρ_X|P_Y) ≅ F_3`, and `N = ker(ρ_Y|P_X)`.

A *Case 1 tuple* is `α_1, α_2 ∈ F` and `β_1, β_3 ∈ N` with
`(*)  β_3^{-1}(α_1α_2)β_3 = α_1β_1α_2β_1^{-1}`.
Its hexagon is
- `x_1 = A_X`, `x_2 = α_1A_X`, `x_3 = α_1β_1α_2A_X`;
- `y_1 = A_Y`, `y_2 = α_1β_1A_Y`, `y_3 = β_3^{-1}A_Y`.

Define the three *corner elements* and the three *corner subgroups*:
- `e_0 = α_1`, `e_1 = β_1α_2β_1^{-1}`, `e_2 = (e_0e_1)^{-1}`, so `e_0e_1e_2 = 1`;
- `F_0 = F`, `F_1 = β_1Fβ_1^{-1}`, `F_2 = β_3^{-1}Fβ_3`.

**Theorem.**

**(M) Membership.** `P ∩ A_XA_Y = P_XP_Y = P_X·F`. For `c ∈ P`,
`c ∈ P_X·F  ⟺  ρ_X(c)^{-1}c ∈ F`,
and `F·P_X` has the mirror-image criterion `cρ_X(c)^{-1} ∈ F`.

**(C) Corners.** `e_i ∈ F_i` for `i = 0, 1, 2`. Only `e_2 ∈ F_2` uses `(*)`, and `e_2 ∈ F_2` is equivalent to
the adjacency `x_3 ~ y_3`.

**(H) Pure bounds.** Some `hA_Y` with `h ∈ P` is adjacent to `x_1, x_2, x_3` iff there is `γ ∈ P_X` with
`e_0, e_1, e_2 ∈ γFγ^{-1}`, i.e. `⟨e_0, e_1⟩ ≤ γFγ^{-1}`. The bound is then `γA_Y`, and every pure bound has this form.

**(V′) Vertex bounds.** With `c_01 = e_1`, `c_12 = β_1^{-1}α_1β_1` and `c_20 = β_3α_1β_3^{-1}`, each
`ρ_X(c_P) = 1`. So the vertex criterion (V) of `h4-i25-joint-certificates-refute-only-vertex-free-tuples` becomes
simply `c_P ∈ F`. Moreover:
- `y_1` is a common bound iff `γ = 1` works;
- `y_3` is a common bound iff `γ = β_3^{-1}` works;
- `y_2` is a common bound iff `γ = β_1` works, and then `y_2 = β_1A_Y`.

So "some hexagon vertex is a pure centre" (VC) says exactly that the witness in (H) can be chosen among the three
corner conjugators `1, β_1, β_3^{-1}`, i.e. that one `F_j` contains all three `e_i`. Equivalently, VC fails iff
`e_0 ∉ F_1 ∪ F_2` and `e_1 ∉ F_0`.

**(T) The conjugates of F are not independent** (certified computation). `x_0 = s_4^2 ∈ N` gives
`x_0p_2x_0^{-1}, x_0p_3x_0^{-1} ∈ F` but `x_0p_1x_0^{-1} ∉ F`. So `F ∩ x_0Fx_0^{-1} ⊇ ⟨p_2, p_3⟩` is nontrivial,
while `x_0Fx_0^{-1} ≠ F`.

This kills the free-product route to VC. If the `P_X`-conjugates of `F` were pairwise equal or free factors of a free
product, then `e_0e_1e_2 = 1` would force VC at once. By (T) they are neither.

**Status of VC and of (H).**
- **Case 1 of the target reduces to (H).** (H) is an intrinsic Helly-type property of the family
  `{γFγ^{-1} : γ ∈ P_X}` inside `ker ρ_X`. (Serre's lemma would give it, for instance, if these conjugates were the vertex
  stabilisers of an action on a tree.)
- **VC is the witness-restricted form.** It is open. It is false in the tree model whenever a tripod centre carries
  the three `e_i`.
- **Searches.** Every search below found **0** tuples, and every hit would have been re-verified in exact Garside
  normal form:
  - VC-failures built from transporter triangles (176 conjugators in `P_X` of length ≤ 2);
  - pair twists (900 conjugators);
  - the w11 vertex search `|α| ≤ 1`, `|β| ≤ 3`. It is now run on 34 of the 36 ordered letter pairs `(α_1, α_2)`,
    including 10 new pairs with 2040 genuine tuples. The 2 missing pairs are the diagonal pairs `α_1 = α_2 = a^{±1}`
    for the first generator `a` of `F`. Each of those exceeds 1200 s even when split four ways, because it is
    dominated by the `β_1, β_3 ∈ C(a)` family. That family has `c_01 = a ∈ F`, so every tuple in it has a vertex centre.
