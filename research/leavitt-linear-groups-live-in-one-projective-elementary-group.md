---
rg: 2
id: leavitt-linear-groups-live-in-one-projective-elementary-group
kind: claim
title: Over a ring with a Leavitt pair every GL_n(R) is the one group R^x, which embeds in PE_N(R) for every N >= 3; so BH for all linear groups over R follows from finite presentation and simplicity of a single PE_N(R), which holds for L_F2(1,2) and fails for every ring containing Q
distinct_from:
  projective-elementary-fp-kernel-criterion: that characterizes when PE_n(R) is finitely presented; this shows that for Leavitt rings the one group PE_N(R) already contains every GL_n(R), so that criterion is the whole question for BH of R-linear groups.
  leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1: that embeds E_n(R) in St_(3n+1)(R) through Leavitt-pair centralizers, one n at a time; this embeds all GL_n(R) at once in E_3(R) through the Leavitt module isomorphism R^n ≅ R and Whitehead's lemma.
  rational-scalars-obstruct-fp-elementary-hosts: that shows PE_N(R) is not finitely presented when Q ⊆ R; this records that this is the only obstruction to the one-group host, and names where it vanishes.
---

**ESTABLISHED.** Lane proof by gq-stv-host, elementary given the cited nodes. Not independently reviewed. No priority
is claimed; items 1 and 2 are standard manipulations.

**Statement.** Let `R` be a unital ring with a Leavitt pair (`t_i s_j = δ_ij`, `s_1 t_1 + s_2 t_2 = 1`).
1. **One linear group.** `R^n ≅ R` as right modules for all `n >= 1`. So `M_n(R) ≅ R` as rings and `GL_n(R) ≅ R^x`.
2. **One host.** For every `N >= 3`, `u ↦ diag(u, u^-1, 1, …, 1)` embeds `R^x` in `E_N(R)` by Whitehead's lemma.
   The image meets the scalar matrices only in `1`. So if the centre of `E_N(R)` consists of scalar matrices, every
   subgroup of every `GL_n(R)`, for all `n` at once, embeds in `PE_N(R) = E_N(R)/Z(E_N(R))`.
3. **Criterion.** Suppose `R` is finitely presented, `N >= 4`, and `PE_N(R)` is simple. By
   `projective-elementary-fp-kernel-criterion`, the single group `PE_N(R)` is then a finitely presented simple host
   for every finitely generated `R`-linear group exactly when both of the following hold:
   - `ker(St_N(R) -> E_N(R))` is finitely normally generated;
   - `Z(E_N(R))` is finitely generated.
4. **Where it holds, where it fails.**
   - **Holds for `R = L_F2(1,2)`**, with nothing new to prove. There `GL_n(R) = EL_n(R) ≅ R^x`
     (`leavitt-gl-equals-el-and-perfect-unit-group`), and `R^x` is finitely presented and simple
     (`leavitt-unit-group-finitely-presented`, `binary-leavitt-unit-group-is-simple`). So the one finitely presented
     simple group `L_F2(1,2)^x` contains every `GL_n(L_F2(1,2))`, for instance every `GL_n(F_2[x])`.
   - **Fails for every `R ⊇ Q`.** The rational scalars make `Z(E_N(R))` infinitely generated
     (`rational-scalars-obstruct-fp-elementary-hosts`, `leavitt-scalar-commutators-block-fp-central-quotients`).
     This includes `R_L`, whose `PE_3(R_L)` contains every `GL_n(Q)` but is not finitely presented.

## Lesson for general BH

**For Leavitt rings the linear world of `R` is a single group.** Matrix size carries no information, and the whole
Boone–Higman question for `R`-linear groups is finite presentation of one projective elementary group. The only
obstruction is central:
- a finitely normally generated Steinberg kernel;
- finitely many central scalars.

**Characteristic.** In positive characteristic both conditions can hold; `L_F2(1,2)^x` is the model case. In
characteristic zero the rational scalars make them fail for every ring. Combined with
`leavitt-steinberg-thompson-extensions-add-nothing`, no extension of such a group by ring or Thompson symmetries
helps, since those fix the scalars. So `GL_n(Q)` needs a host in which the central `Q^x` of `PE`/`St` is conjugated
non-trivially. This is a characteristic-zero phenomenon, the scale-shift gate, and not a matrix-size or linear-algebra
phenomenon.
