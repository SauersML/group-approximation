---
rg: 2
id: fp-groups-have-no-multiplier-product-completions-proof
kind: route
title: Every nonzero combination of the factor extensions is non-split over a dense finitely presented subgroup, and a presentation with r relators leaves room for at most r of them
target: fp-groups-have-no-multiplier-product-completions
requires:
  - alternating-groups-have-nonzero-schur-multiplier
---

Notation. `ι : Γ -> Γ^` is the canonical map, which need not be injective. For
a finite `E <= I`, `Q_E = prod_(i in E) Q_i`, and `pr_E : U -> Q_E` is the
projection. `j_E' : Q_E -> Q_E'` (for `E <= E'`) is the inclusion with trivial
coordinates outside `E`; it is a section of the projection `Q_E' -> Q_E`.

**Step 1 (the dense subgroup).** Put `Δ = ι^(-1)(U)`, of finite index in `Γ`. By
Reidemeister--Schreier, `Δ` is finitely presented. Fix a presentation
`< x_1, ..., x_n | r_1, ..., r_r >`. `ι(Δ) = ι(Γ) ∩ U` is dense in the open set
`U`. So `ρ_E = pr_E ∘ ι : Δ -> Q_E` is onto for every finite `E`.

**Step 1a (extension fact).** Every homomorphism from `Δ` onto a finite group
`P` extends to a continuous homomorphism `F : U -> P` with `F ∘ ι = f`. This is
Step 0 of `simple-product-completions-block-regular-tree-actions-proof`, whose
argument does not use injectivity of `ι`: well-definedness uses only
`ι^(-1)(ker π) = N_0`. So `ker F` is open, and it contains the subgroup of
elements trivial on some finite `E' <= I`. Hence `F = F' ∘ pr_E'` for some
homomorphism `F' : Q_E' -> P`.

**Step 2 (the combined extension).** Fix `p`, and let `E` be a finite set of
indices satisfying `(MP1)`. For `i in E` choose a non-split central extension
`1 -> Z/p -> Ẽ_i -> Q_i -> 1`. Put `P = prod_(i in E) Ẽ_i`,
`A = (Z/p)^E <= Z(P)` and `q : P -> Q_E`. For a nonzero linear form
`λ : A -> Z/p`, put `P_λ = P / ker λ`, a central extension
`1 -> Z/p -> P_λ -> Q_E -> 1` with map `q_λ`.

**Step 3 (`P_λ` is non-split over `Q_E`).** Pick `j` with `λ_j != 0` on the
`j`-th coordinate of `A`. The preimage of the factor `Q_j` in `P_λ` is the image
of `Ẽ_j × prod_(i != j) A_i`. The map from `Ẽ_j` to it is onto: a coordinate in
`A_i` changes `λ` by a scalar that a suitable element of `A_j` matches, since
`λ_j != 0`. Its kernel is `Ẽ_j ∩ ker λ = ker(λ_j) = 1`. So the preimage is
isomorphic to `Ẽ_j` over `Q_j`. A section of `q_λ` would restrict to a section
of `Ẽ_j -> Q_j`, which does not exist.

**Step 4 (`P_λ` does not split over `Δ`).** Suppose `s : Δ -> P_λ` is a
homomorphism with `q_λ ∘ s = ρ_E`. Then `s(Δ)` maps onto `Q_E`, and `s(Δ) ∩ Z/p`
is `1` or `Z/p`.
- If it is `1`, then `q_λ` restricted to `s(Δ)` is an isomorphism onto `Q_E`, and
  its inverse is a section of `q_λ`. This contradicts Step 3.
- If it is `Z/p`, then `s` is onto `P_λ`. By Step 1a, `s = F' ∘ pr_E' ∘ ι` for
  some finite `E' ⊇ E` and some `F' : Q_E' -> P_λ`. The maps `q_λ ∘ F' ∘ pr_E'`
  and `pr_E` are continuous into a discrete group and agree on the dense set
  `ι(Δ)`, so they agree on `U`. Since `pr_E'` is onto, `q_λ ∘ F'` is the
  projection `Q_E' -> Q_E`. Then `F' ∘ j_E'` is a section of `q_λ`, which again
  contradicts Step 3.

**Step 5 (counting with the presentation).** Choose `p_k in P` with
`q(p_k) = ρ_E(x_k)`. Each relator value `v_l = r_l(p_1, ..., p_n)` lies in `A`,
because `ρ_E` kills `r_l`. Let `e_(lk)` be the exponent sum of `x_k` in `r_l`,
and let `R <= (Z/p)^r` be the image of `b |-> (sum_k e_(lk) b_k)_l`. Every lift
of `ρ_E(x_k)` to `P_λ` is the image of `p_k` times some `b_k in Z/p`, since `A`
maps onto `Z/p`. Because `Z/p` is central, the relators evaluate on the new
lifts to `λ(v_l) + sum_k e_(lk) b_k`. By von Dyck's theorem, `ρ_E` lifts to
`P_λ` if and only if

```text
( λ(v_l) )_(l = 1..r)  lies in  R.                                      (MP2)
```

The map `Λ : Hom(A, Z/p) -> (Z/p)^r / R`, `λ |-> [(λ(v_l))_l]`, is linear.
Step 4 says `(MP2)` fails for every `λ != 0`, so `Λ` is injective, and

```text
|E| = dim Hom(A, Z/p)  <=  r - dim R  <=  r.                            (MP3)
```

**Step 6 (conclusion).** `(MP3)` holds for every finite set `E` of indices
satisfying `(MP1)`, so there are at most `r` of them.

For the alternating consequence: `Alt(n)` is perfect for `n >= 5`, and
`H_2(Alt(n); Z)` has even order by
`alternating-groups-have-nonzero-schur-multiplier`. By the universal
coefficient theorem, `H^2(Alt(n); F_2) = Hom(H_2(Alt(n); Z), F_2) != 0`. So
`Alt(n)` has a non-split central extension by `Z/2`, and `(MP1)` holds at
`p = 2` for every `n >= 5`. `∎`
