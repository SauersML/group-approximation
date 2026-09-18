---
rg: 2
id: steinberg-simple-quotients-of-q-rings-reduce-to-pe-n
kind: claim
title: Simple quotients of St_N(R) reduce to PE_N(R/I) under central unstable K_2 and the sandwich property; injective stability forces central K_2, so for Leavitt-type rings containing Q a finitely presented simple Steinberg quotient needs U_N ≠ 0 or a non-simple PE_N
distinct_from:
  sandwiched-e-n-has-only-projective-simple-quotients: that classifies simple quotients of E_N(R); this lifts the classification to St_N(R), which is the finitely presented group actually available, and adds the centrality criterion from injective stability.
  faithful-pair-finite-steinberg-actions-need-noncentral-k2: that concerns type (A) actions of St_N; this concerns St_N's simple quotients as hosts.
  steinberg-resolvent-shell-envelope-is-finitely-presented: that uses St_N(R_L) as the input of a shell envelope and is unaffected here; this concerns St_N(R_L) (and its quotients) as the host itself.
---

**ESTABLISHED** for parts 1–4 (lane proof, elementary, inline; not reviewed; no novelty
claimed). Part 5 composes landed nodes.

## Statement

Let `R` be a nonzero unital ring, `N >= 3`, and `S = St_N(R)/M` a nonabelian simple
group. Write `K_2(N,R) = ker(St_N(R) -> E_N(R))`, `ι: St_N(R) -> St(R)` for
stabilization and `U_N = ker(ι|K_2(N,R))`.

1. **Levels.** `I_M = {r : x_12(r) ∈ M}` is a proper two-sided ideal, and `x_ij` induces an
   injection `(R/I_M, +) -> S`. If `R` is simple, `I_M = 0`, so `S` contains `(R,+)`, and if
   moreover `Q ⊆ R` unitally, the image of `St_N(Q)` in `S` is a perfect central extension
   of `PSL_N(Q)`.
2. **Central K_2 kills K_2.** If `K_2(N,R)` is central in `St_N(R)`, then `K_2(N,R) <= M`,
   and `S` is a quotient of `PE_N(R)`.
3. **Classification.** If in addition `(R, N)` has the sandwich property SW_N of
   `sandwiched-e-n-has-only-projective-simple-quotients`, then `S ≅ PE_N(R/I_M)`.
4. **Injective stability gives centrality.** If `U_N = 0`, then `K_2(N,R)` is central in
   `St_N(R)`. More generally `[K_2(N,R), St_N(R)] <= U_N`.
5. **Leavitt-type rings containing Q.** Suppose `R ⊇ Q` unitally, `R` contains a unital
   binary Leavitt pair, `U_N = 0` and SW_N holds. Then **no** nonabelian simple quotient of
   `St_N(R)` is finitely presented, for any `N >= 3`.

## Application to the Leavitt resolvent ring `R_L`

`R_L` is finitely presented and simple, contains `Q` (indeed `Q̄`) unitally and a Leavitt
pair (`leavitt-resolvent-ring-is-fp-simple-of-char-zero`), so `St_N(R_L)` is finitely
presented for `N >= 5`, is finitely generated, and has simple quotients (Zorn), each
containing `(R_L, +)` by part 1. By part 5, one of them can be finitely presented only if

- `U_N ≠ 0` (unstable `K_2(N, R_L)` does not inject into `K_2(R_L) ≅ Q^x`), or
- `PE_N(R_L)` is not simple (SW_N fails for `R_L`).

This is in tension with gate 1 of the shell route: `st-n-leavitt-resolvent-word-problem-reduces-to-k2`
and `leavitt-refinement-identifies-unstable-k2-levels` want `U_N = 0` (it gives solvable word
problem for `St_N(R_L)`). If `U_N = 0` and SW_N holds, then `St_N(R_L)` is a good shell
*input* but none of its simple quotients is a finitely presented *host*. Part 4 also
settles `k2-central-in-steinberg-groups-of-leavitt-resolvent-ring` conditionally: that node
follows from `U_N = 0`.

## Proof

*Part 1.* The level of a normal subgroup of `St_N(R)` is a two-sided ideal by the same
commutator identities as in `E_N` (`[x_ik(a), x_kj(b)] = x_ij(ab)` for distinct `i,k,j`, and
`x_ij(a)x_ij(b) = x_ij(a+b)`), and if it were `R` then `M` would contain every `x_ij(r)`,
hence all of `St_N(R)`. So `I_M` is proper, and `x_ij(r) ∈ M` iff `r ∈ I_M` gives the
injection. For `R` simple, `I_M = 0`.

Now let `Q ⊆ R` and let `L` be the kernel of `St_N(Q) -> S`. It is normal in `St_N(Q)` and
does not contain `x_12(1)` (as `1 ∉ I_M`). Let `Z̃` be the preimage in `St_N(Q)` of the
centre of `SL_N(Q)`. `Z̃` is central: for `z ∈ Z̃`, every `[z, x]` lies in the central
subgroup `K_2(N,Q)`, so `x ↦ [z,x]` is a homomorphism from the perfect group `St_N(Q)` to an
abelian group, hence trivial. The image of `L` in the simple group `PSL_N(Q)` is trivial
or everything. If everything, `L Z̃ = St_N(Q)`, and then
`St_N(Q) = [St_N(Q), St_N(Q)] = [L Z̃, L Z̃] = [L, L] <= L`, contradicting `x_12(1) ∉ L`.
So `L <= Z̃` is central and `St_N(Q)/L` is a perfect central extension of `PSL_N(Q)`.

*Part 2.* The image of the central subgroup `K_2(N,R)` in `S` is central, and a nonabelian
simple group has trivial centre; so `K_2(N,R) <= M` and `S` is a quotient of `E_N(R)`.
The image of `Z(E_N(R))` is again central, hence trivial.

*Part 3.* `S` is a nonabelian simple quotient of `E_N(R)`; apply
`sandwiched-e-n-has-only-projective-simple-quotients`, part 2. Its ideal `I_H` for
`H = ker(E_N(R) -> S)` equals `I_M`, since `x_12(r) ∈ M` iff its image lies in `H`.

*Part 4.* `K_2(N,R)` is normal in `St_N(R)` (a kernel), so for `k ∈ K_2(N,R)` and
`x ∈ St_N(R)` the commutator `[k, x]` lies in `K_2(N,R)`. Its image under `ι` is
`[ι k, ι x] = 1`, because the stable `K_2(R)` is central in `St(R)` (Kervaire; Milnor,
*Introduction to algebraic K-theory*, Thm. 5.1 — recalled, not re-read). So `[k,x] ∈ U_N`.

*Part 5.* By parts 2–4, `S ≅ PE_N(R/I)` with `I = I_M` proper. `Q ∩ I = 0`, so `R/I`
contains `Q` unitally, and the image of the Leavitt pair is a unital Leavitt pair in the
nonzero ring `R/I`. By `ibn-failure-makes-rational-scalars-elementary`, part 3,
`PE_N(R/I)` is not finitely presented for any `N >= 3`.
