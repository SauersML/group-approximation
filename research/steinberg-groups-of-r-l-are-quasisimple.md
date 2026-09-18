---
rg: 2
id: steinberg-groups-of-r-l-are-quasisimple
kind: claim
title: St_N(R_L) is quasisimple for every N >= 3, with centre H_2(PE_N(R_L)) not finitely generated and H_2(E_N(R_L)) = Q^x; every GL_n(Q) embeds in St_10(R_L) missing the centre, hence in the simple group PE_10(R_L)
distinct_from:
  leavitt-resolvent-k2-stability-holds: that proves K_2(N,R_L) = Q^x and its centrality; this uses it to determine every normal subgroup of St_N(R_L), its centre, and the Schur multipliers of E_N(R_L) and PE_N(R_L).
  steinberg-simple-quotients-of-q-rings-reduce-to-pe-n: that shows, under U_N = 0 and SW_N, that no simple quotient of St_N(R) is finitely presented; this shows that for R_L every proper normal subgroup is central, so PE_N(R_L) is the only simple quotient.
  leavitt-resolvent-ring-has-two-sided-division: that embeds GL_(N-2)(Q) in PE_N(R_L), one N at a time; this puts every GL_n(Q) in the one simple group PE_10(R_L), through St_10(R_L).
  leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1: that embeds every GL_n(Q) in St_10(R_L); this shows the image meets the centre trivially.
---

**ESTABLISHED** through `steinberg-groups-of-r-l-are-quasisimple-proof`. Lane proof, not independently reviewed.
It is elementary given the cited nodes, van der Kallen's statement that `H_2(St_n(R)) = 0` for `n >= 5` (read at
source), and the standard facts on universal central extensions (Milnor, *Introduction to algebraic K-theory*, §5,
recalled). No priority is claimed.

**Setting.** `R_L` is the ring of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`, and `N >= 3`.
- `S_N = St_N(R_L)`, with `φ : S_N -> E_N(R_L)` and kernel `K_2(N, R_L)`.
- `Z_E` is the centre of `E_N(R_L)`: the scalar matrices `λ I_N` with `λ` a central unit of `R_L` and `λ I_N` in `E_N`.
- `PE_N(R_L) = E_N(R_L) / Z_E`, and `A_N = φ^(-1)(Z_E)`.

**Statement.**
1. **Normal subgroups.** Every normal subgroup of `S_N` is either `S_N` or contained in `A_N`, and `A_N = Z(S_N)`.
   So `S_N` is quasisimple: it is perfect, and `S_N / Z(S_N) ≅ PE_N(R_L)` is simple.
   - `PE_N(R_L)` is the only simple quotient of `S_N`, and also of `E_N(R_L)`.
   - `A_N` is the unique maximal normal subgroup of `S_N`.
2. **Centre.** There is an exact sequence `1 -> K_2(N, R_L) -> Z(S_N) -> Z_E -> 1`, with `K_2(N, R_L) ≅ Q^x` and
   `Z_E ⊇ Q^x I_N`. So `Z(S_N)` is not finitely generated.
3. **Schur multipliers.** `H_2(S_N; Z) = 0`. So `S_N` is the universal central extension both of `E_N(R_L)` and of
   `PE_N(R_L)`. Hence:
   - `H_2(E_N(R_L); Z) ≅ Q^x`;
   - `H_2(PE_N(R_L); Z) ≅ Z(S_N)`, which is not finitely generated.

   This gives a second proof that `PE_N(R_L)` is not finitely presented, independent of the scalar argument of
   `ibn-failure-makes-rational-scalars-elementary`.
4. **GL_n(Q).** For every `n >= 1`, `GL_n(Q)` embeds in `S_10 = St_10(R_L)` with image meeting `Z(S_10)` trivially.
   So `GL_n(Q)` embeds in the finitely generated simple group `PE_10(R_L)`, which has solvable word problem.

## Reading for Boone--Higman

- **A quasisimple overgroup.** `St_10(R_L)` is finitely presented and Kazhdan, and it has solvable word problem
  (`leavitt-resolvent-k2-stability-holds`, item 4). It is simple modulo its centre, and it contains every `GL_n(Q)`
  with trivial intersection with that centre. What stands between this group and a finitely presented simple
  overgroup of `GL_n(Q)` is exactly the centre, which is not finitely generated. If the centre of a finitely presented
  group `Γ` is finitely generated, then `Γ / Z(Γ)` is finitely presented.
- **The Steinberg-quotient route through `R_L` is closed.** Every simple quotient of `St_N(R_L)` is `PE_N(R_L)`,
  which is not finitely presented. `U_N = 1` removes the alternative "quotient of `U_N`" left open in
  `leavitt-steinberg-hosts-must-live-in-the-stabilization-kernel`, part 2.
  - A finitely presented simple group built from `R_L` must therefore come from another construction, such as the
    shell envelope of `steinberg-resolvent-shell-envelope-is-finitely-presented`, whose gate 1 is closed by
    `leavitt-resolvent-k2-stability-holds`.
