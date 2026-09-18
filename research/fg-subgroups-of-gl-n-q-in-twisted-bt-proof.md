---
rg: 2
id: fg-subgroups-of-gl-n-q-in-twisted-bt-proof
kind: route
title: Finitely generated subgroups of GL_n(Q) lie in B_A, and a type (A) actor sits in its finitely presented simple twisted Brin--Thompson group together with kV
target: fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups
requires:
  - fp-self-similar-subgroups-satisfy-permutational-boone-higman
  - twisted-brin-thompson-finite-presentation-criterion
  - rationals-embed-in-brin-thompson-group-2v
  - countable-virtually-abelian-groups-embed-in-2v
---

**Item 1.** `Q` is algebraic over `Q`. So by part (b) of
`fp-self-similar-subgroups-satisfy-permutational-boone-higman`, the finitely
generated group `H` lies in a finitely presented self-similar group, and hence
in `B_A`. By the definition of `B_A` there is a group `Γ >= H` with an action on
a set `S` of type (A). Type (A) means the action is faithful, `Γ` is finitely
presented, point stabilizers are finitely generated, and there are finitely many
orbits of two-element subsets. By `twisted-brin-thompson-finite-presentation-criterion`
(Zaremsky, arXiv:2405.18354, Theorem A), `SV_Γ` is finitely presented. The
action is faithful, so `SV_Γ` is simple and contains `Γ`, hence `H`.

**Item 2.** This is a hand check from the definition in the survey
arXiv:2306.16356v3, §4, "Twisted Brin--Thompson groups": `SV_Γ` is the group of
all homeomorphisms of `C^S` that locally agree with elements of the restricted
wreath product `V ≀ Γ = (⊕_S V) ⋊ Γ`. Here `C = {0,1}^ω`, and `C^S` has the
product topology.
- Fix `T ⊆ S` with `|T| = k`, and write `C^S = C^T × C^(S∖T)`. For `h ∈ kV`,
  acting on `C^T`, put `ĥ(x, z) = (h(x), z)`. Then `h ↦ ĥ` is an injective
  homomorphism into `Homeo(C^S)`.
- Let `h` map the brick `u_1C × ⋯ × u_kC` onto `v_1C × ⋯ × v_kC` by prefix
  replacement. Let `p` be a point of that brick. Choose nonempty words `w_i`
  with `p_i ∈ u_i w_i C`. Then `u_i w_i C` and `v_i w_i C` are proper cones.
- For each `i` pick `f_i ∈ V` with `f_i(u_i w_i y) = v_i w_i y` for all `y`.
  Such an `f_i` exists because any prefix replacement between two proper cones
  of `C` extends to an element of `V`: their complements are finite unions of
  cones, which can be refined to the same number of cones and matched.
- Then `ĥ` agrees with `(f_i)_{i ∈ T} ∈ ⊕_S V` on the neighbourhood
  `∏_i u_i w_i C × C^(S∖T)` of `p`.
- So `ĥ ∈ SV_Γ`, and `kV <= SV_Γ`.

If `H` is infinite, then so is `Γ`. A faithful action of an infinite group is on
an infinite set, so `S` is infinite and every `kV` embeds. Then
`rationals-embed-in-brin-thompson-group-2v` and
`countable-virtually-abelian-groups-embed-in-2v` give `(Q,+) <= 2V <= SV_Γ` and
every countable virtually abelian group inside `SV_Γ`.

**Examples.** `GL_n(Z[1/m])` is finitely generated, being an S-arithmetic group.
It contains `BS(1,2)` when `2 | m` and `n >= 2`, and it contains `SL_3(Z)` and
`H_3(Z)` when `n >= 3`. ∎
