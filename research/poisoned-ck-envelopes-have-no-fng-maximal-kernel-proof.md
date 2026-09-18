---
rg: 2
id: poisoned-ck-envelopes-have-no-fng-maximal-kernel-proof
kind: route
title: Amalgamate the simple core with an inseparable Heisenberg group along the normal generator, then apply Chatterji--Kassabov
target: poisoned-ck-envelopes-have-no-fng-maximal-kernel
requires: [inseparable-heisenberg-shift-group-poisons-its-center, chatterji-kassabov-normal-generator-embedding, proper-normal-subgroups-miss-the-normally-generating-core, fp-quotient-iff-kernel-finitely-normally-generated, ck-steinberg-marked-cover, fp-group-embeds-in-fp-derived-subgroup]
artifacts:
  - experiments/ck-poisoned-envelope-2026-09-17/heisenberg_model_check.py
---

Let `S` be finitely generated, computably presented, infinite and simple, and let
`1 != s in S` have order `k in {2,3,...} ∪ {∞}`.

## Step 1. The poisoned input

Take `Q_k` and its central element `c` of order exactly `k` from
`inseparable-heisenberg-shift-group-poisons-its-center`. Let

    G = S *_{<s> = <c>} Q_k ,

the amalgamated free product identifying `s^i` with `c^i`. This is legitimate because both
cyclic groups have order `k`.

- **Presentation.** A presentation of `G` is the union of a computable presentation of `S`, the
  r.e. presentation of `Q_k`, and the one relator `s = c`. So `G` is finitely generated and
  computably presented.
- **Embedding.** By the normal form theorem for amalgamated free products (Serre, *Trees*, §I.1,
  Thm. 1; Lyndon--Schupp, *Combinatorial Group Theory*, Thm. IV.2.6), both factors embed in `G`.
  So `S <= G`, `Q_k <= G`, and `s = c != 1` in `G`.

## Step 2. The envelope

`chatterji-kassabov-normal-generator-embedding` (CK Theorem 3, quoted verbatim in that node)
applies to the finitely generated recursively presented group `G` and the nontrivial element `s`.
It gives an embedding `G <= Γ` with `Γ` finitely presented, property (T), and `Γ = <<s>>_Γ`. So
`S <= Γ` with `Γ = <<s>>_Γ`, which is exactly the situation of
`ck-envelope-has-a-finitely-normally-generated-maximal-kernel`.

## Step 3. Every nontrivial quotient is undecidable

Let `N` be a proper normal subgroup of `Γ` and `ρ : Γ -> Γ/N` the quotient map. Since
`<<s>>_Γ = Γ` and `N != Γ`, we have `s ∉ N`. This is also the content of
`proper-normal-subgroups-miss-the-normally-generating-core`: `N ∩ S = 1`. So `ρ(c) = ρ(s) != 1`.

Restrict `ρ` to `Q_k <= Γ`. This is a homomorphism not killing `c`, so by the poisoning theorem
`ρ(Q_k)` has unsolvable word problem. `ρ(Q_k)` is a finitely generated subgroup of the finitely
generated group `Γ/N`, and a solvable word problem would pass to it. So `Γ/N` has unsolvable word
problem. This proves clause 2.

## Step 4. No maximal kernel is r.e.

Let `M` be a maximal proper normal subgroup, so `L = Γ/M` is simple and nontrivial. Suppose `M` is
recursively enumerable, i.e. `L` is recursively presented on the images of the finitely many
generators of `Γ`. Then `L` has solvable word problem, by Kuznetsov's two enumerations:

- to see `w = 1`, enumerate consequences of the relators of `L`;
- to see `w != 1`, fix a generator `x != 1` of `L` and enumerate consequences of the relators
  together with `w`, waiting for `x`. Simplicity makes `<<w>> = L` for `w != 1`.

One of the two searches halts, and they cannot both halt. This contradicts Step 3, so `M` is not
r.e.

A finitely normally generated `M` is r.e. (enumerate products of conjugates of its normal
generators and of the relators of `Γ`). So no maximal kernel is finitely normally generated. By
`fp-quotient-iff-kernel-finitely-normally-generated`, no maximal quotient is finitely presented.
This proves clause 3.

## Step 5. The general poison obstruction

Replace `Q_k` by any finitely generated `P <= Γ` containing an element `1 != t in S` that is
poisoned in `P`. Steps 3 and 4 use only that proper normal subgroups miss `S`, which is
`proper-normal-subgroups-miss-the-normally-generating-core`, and that `t` is poisoned. So they go
through verbatim.

## Step 6. Transfer to the marked Steinberg cover

`ck-steinberg-marked-cover` takes any finitely presented `H` and `T` with `H <= [T,T]` and
`1 != g in H`. It produces a finitely presented property-(T) group `Γ'` with
`St_4(U) ->> Γ' ->> EL_4(U)`, an embedding `H -> Γ'`, and `Γ' = <<g>>_{Γ'}`. Take `H = Γ` from
Step 2 and `g = s`. The required `T` exists by `fp-group-embeds-in-fp-derived-subgroup`.

Then `S, Q_k <= G <= H <= Γ'` and `Γ' = <<s>>_{Γ'}`, so Step 5 applies with `P = Q_k`.
Every nontrivial quotient of `Γ'` has unsolvable word problem, and no maximal kernel of `Γ'` is
r.e. ∎

## Why each prerequisite is used

- **The poisoning theorem** supplies the element that must survive and cannot survive decidably.
- **CK Theorem 3** supplies a finitely presented envelope for an input that is merely recursively
  presented. It is used exactly with its stated hypotheses, which is what makes this a
  counterexample to the target *as stated*.
- **Core survival** guarantees that the poisoned element survives in every proper quotient.
- **The Tietze criterion** turns "not r.e." into "no finitely presented maximal quotient".
- **The marked-cover node and the derived-subgroup embedding** show that the covering structure
  does not screen the poison out.
