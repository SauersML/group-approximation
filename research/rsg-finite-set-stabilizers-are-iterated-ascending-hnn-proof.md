---
rg: 2
id: rsg-finite-set-stabilizers-are-iterated-ascending-hnn-proof
kind: route
title: Upgrade the BBMZ finite-generation proof for finite-set stabilizers to an iterated ascending HNN decomposition, then apply the Belk-Zaremsky F_n criterion and the quasi-retraction
target: twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family
requires:
  - twisted-brin-thompson-groups-quasi-retract-onto-acting-group
  - hyperbolic-groups-undistortedly-embed-in-fp-simple-groups
  - contracting-rsgs-embed-in-fp-simple-groups
---

Lane proof, not independently reviewed. The BBMZ references are to arXiv:2309.06224v3 TeX (copy at
`$GQ/src/bh-free-03/bbmz2-2309.06224.tex`), read at source:
- `prop:CyclicStabilizers`: germ groups at rational points are virtually cyclic, generated up to finite
  index by a canonical-similarity germ;
- `prop:fin_gen_stabs`: the finite-generation proof we upgrade here;
- `cor:MappingConesWithV`;
- `thrm:RSGCharacterization`;
- `prop:HighlyTransitiveAction`.

The Belk–Zaremsky references are to arXiv:2001.04579, TeX copy `$GQ/src/bh-typeA-universal/bz-2001.04579.tex`:
Theorem 4 (`thm:FinitenessTheorem`, l.178) and Theorem 2 (`thm:quasi-retracts`, l.164).

## Item 1

Let `S' = {ω_1, …, ω_n}` be rational, `ω_i = σ_i τ_i^∞` with `τ_i` not a proper power.

**Setup.**
- Take the `σ_i` so long that the cones `U_i = C_{σ_i}` are pairwise disjoint and `U = ⊔ U_i ≠ E`, as
  in `prop:fin_gen_stabs`.
- By `cor:MappingConesWithV`, applied to `{U_j}_j -> {C_{σ_iτ_i}} ∪ {U_j}_{j≠i}`, there are
  `f_i ∈ V_{Γ,E} <= Γ` acting on `U_i` as the canonical similarity `U_i -> C_{σ_iτ_i}` and as the
  identity on `U_j` for `j ≠ i`. The hypotheses hold: types agree, `t(σ_iτ_i) = t(σ_i)`, and both unions
  are proper.
- Then `f_i` fixes `S'`, has trivial germ at `ω_j` for `j ≠ i`, and has germ `[f_i]` at `ω_i`. That germ
  has infinite order and generates a finite-index subgroup of `[Γ]_{ω_i}` (`prop:CyclicStabilizers`).
  Also `f_i^m(U_i) = C_{σ_iτ_i^m}` shrinks to `ω_i`.

**The chain of subgroups.** For `0 <= k <= n` let `B_k` be the set of `g ∈ Γ` that satisfy all of:
- `g` is the identity on `U_{k+1} ∪ ⋯ ∪ U_n`;
- `g` fixes `ω_1, …, ω_k`;
- `[g]_{ω_i} ∈ ⟨[f_i]⟩` for `i <= k`.

Then:
- `B_0 = Fix_Γ(U)`. BBMZ (proof of `prop:fin_gen_stabs`, via `thrm:RSGCharacterization`) identify it
  with the full RSG with nucleus `Nuc` on `E ∖ U`, a member of `𝓕(Γ)`.
- `B_n` is the preimage of `∏_i ⟨[f_i]⟩` under the germ map `Fix_Γ(S') -> ∏_i [Γ]_{ω_i}`. That
  product has finite index in `∏_i [Γ]_{ω_i}`, so `B_n` has finite index in `Fix_Γ(S')`, which has
  finite index in `Stab_Γ(S')`.

**Each step is an ascending HNN extension.** Fix `k >= 1`.
- **Membership.** `f_k ∈ B_k`, and `B_{k-1} <= B_k`: an element that is the identity on `U_k` fixes `ω_k`
  with trivial germ.
- **Conjugation.** `f_k` is the identity on every `U_j` with `j ≠ k`. So conjugation by `f_k` preserves the
  conditions at `ω_i` (`i < k`) and on `U_{>k}`. Since `f_k^{-1}(U_k) ⊇ U_k`, we get
  `f_k^{-1} B_{k-1} f_k <= B_{k-1}`. So `φ(b) = f_k^{-1} b f_k` is an injective endomorphism of `B_{k-1}`.
- **The union.** `⋃_m f_k^m B_{k-1} f_k^{-m}` is the set of elements of `B_k` with trivial germ at
  `ω_k`. Such an element is the identity on a neighbourhood of `ω_k`, and that neighbourhood contains
  `C_{σ_kτ_k^m} = f_k^m(U_k)` for large `m`.
- **Generation.** Every `b ∈ B_k` has `[b]_{ω_k} = [f_k]^m` for some `m`, and `f_k^{-m} b` has trivial
  germ at `ω_k`. So `B_k = ⟨B_{k-1}, f_k⟩`.
- **Conclusion.** `⟨f_k⟩` meets the union trivially, because `[f_k]` has infinite order. So `B_k` is
  `(⋃_m f_k^m B_{k-1} f_k^{-m}) ⋊ ⟨f_k⟩`, which is the ascending HNN extension `B_{k-1} *_φ`.

**Finiteness.** An ascending HNN extension of a group of type F_n is of type F_n. It is the fundamental
group of a graph of groups with one vertex and one edge, both of type F_n (standard; e.g. Geoghegan,
*Topological Methods in Group Theory*, §7.2). Finite-index overgroups inherit F_n. So `Stab_Γ(S')` is
F_n whenever `B_0` is.

## Items 2–4

- **Item 2.** `Γ` acts highly transitively, hence oligomorphically, on the countable set `S`
  (`prop:HighlyTransitiveAction`). Finite subsets of `S` consist of rational points. So Belk–Zaremsky
  Theorem 4 applies with the stabilizers of item 1 and with `Γ ∈ 𝓕(Γ)`.
- **Item 3.** `SV_Γ` is finitely generated. Belk–Zaremsky Theorem 2
  (`twisted-brin-thompson-groups-quasi-retract-onto-acting-group`) makes `Γ` a quasi-retract of `SV_Γ`,
  and Alonso's theorem (quasi-retracts of F_n groups are F_n, as recalled in Belk–Zaremsky l.199) gives
  `Γ` of type F_n.
- **Item 4.** Combine item 2 with `n = ∞` and `hyperbolic-groups-undistortedly-embed-in-fp-simple-groups`.
  `SV_Γ` is simple by `contracting-rsgs-embed-in-fp-simple-groups`. ∎

## Calibration

- **Thompson's `V`.** For `V = V_{Γ,E}` with trivial nucleus, `𝓕` consists of Higman–Thompson-type
  groups, all of type F_∞. Item 1 then gives F_∞ stabilizers of finite sets of rational points. This
  agrees with `higman-thompson-rational-point-fixers-are-f-infinity`.
- **`n = 1`.** Item 1 recovers exactly the BBMZ finite-generation argument.

## Lesson for general BH

The argument uses only three features of `Γ`: fullness, virtually cyclic germs at rational points, and
elements that contract one cone while fixing others. Any full-group host with these features has finite-set
stabilizers of the same finiteness type as its rigid subgroups. The type (A) and F_n stabilizer
hypotheses are therefore never the bottleneck for such hosts.
