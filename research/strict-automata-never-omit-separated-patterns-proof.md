---
rg: 2
id: strict-automata-never-omit-separated-patterns-proof
kind: route
title: Periodic configurations of a sofic quotient lie in the image, and finitely many such quotients combine into one
target: strict-automata-never-omit-separated-patterns
requires:
  - injective-automata-restrict-to-schreier-graph-automata
  - sofic-groups-are-surjunctive
  - elek-szabo-sofic-permanence
---

Complete proof. Notation as in the target. `(k.x)(g) = x(k^(-1) g)`, and `τ` commutes with every shift.

## Imports, verbatim

- `injective-automata-restrict-to-schreier-graph-automata`, item 4: "For normal `H`, `tau_S` is the automaton over
  `G/H` with memory `MH/H`. So `Fix_H` lies in `X` whenever `G/H` is surjunctive." Here `Fix_H` is "the
  configurations constant on the right cosets `Hg`". That node assumes a cellular left inverse `σ`. Every
  injective automaton has one: the inverse on `X` is continuous and commutes with shifts, so Curtis–Hedlund–Lyndon
  applies, as in item 4 of `separated-omitted-patterns-cofinite-proof`. Item 1 below also gives a direct proof.
- `sofic-groups-are-surjunctive`: "Let `G` be a sofic group and `A` a finite alphabet. Every injective cellular
  automaton `A^G -> A^G` is surjective."
- `elek-szabo-sofic-permanence`, Theorem 1: "The class of sofic groups is closed under the following
  constructions: 1. direct products, subgroups, inverse limits, direct limits".

## Item 1. Periodic points

A direct proof, so that item 1 does not rest on the left inverse.

- Let `N ⊲ G` and `Fix(N) = {x : n.x = x for all n ∈ N}`. These are the configurations constant on the cosets
  `gN = Ng`, and `x -> (gN -> x(g))` identifies `Fix(N)` with `A^(G/N)`.
- `τ(Fix(N)) ⊆ Fix(N)`, since `n.τ(x) = τ(n.x) = τ(x)`.
- On `Fix(N)`, `τ(x)(g) = μ((x(gm))_(m ∈ M))`, and `x(gm)` depends only on `gmN = (gN)(mN)`. So `τ` acts on
  `A^(G/N)` as the automaton `τ_N` with memory `MN/N`. It is injective, being a restriction of `τ`.
- If `G/N` is surjunctive, `τ_N` is onto, so `Fix(N) = τ(Fix(N)) ⊆ X`.

## Item 2. No omitted letter

- Take `N = G`. Then `G/N` is trivial, hence finite and surjunctive, and `Fix(G)` is the set of constant
  configurations. Item 1 puts every constant configuration in `X`, so every letter occurs.
- Equivalently, `τ` maps the finite set of constants injectively into itself, so it permutes them.

## Item 3. No separated omitted pattern

**Step 1. Consistent patterns occur.** Let `N ⊲ G` with `G/N` sofic. Suppose `w ∈ A^F` satisfies
`w(f) = w(f')` whenever `f^(-1) f' ∈ N`. Define `x` by `x(g) = w(f)` if `g ∈ fN` for some `f ∈ F`, and a fixed
letter otherwise. This is well defined by the hypothesis, and `x ∈ Fix(N)` restricts to `w`. `G/N` is
surjunctive by `sofic-groups-are-surjunctive`, so `x ∈ X` by item 1. So `w` is not omitted.

**Step 2. Combining quotients.** Let `w ∈ A^F` be omitted. Put `P = {f^(-1) f' : f, f' ∈ F, w(f) ≠ w(f')}`. It
is finite and does not contain `1`. Suppose no `p ∈ P` lies in `Σ(G)`.
- For each `p ∈ P` choose `N_p ⊲ G` with `G/N_p` sofic and `p ∉ N_p`. Put `N = ∩_(p ∈ P) N_p`, which is normal.
- `g -> (g N_p)_p` embeds `G/N` into `∏_p G/N_p`. This finite product is sofic by the Elek–Szabó import
  (direct products), and so is its subgroup `G/N` (subgroups).
- `P ∩ N = ∅`, so `w` is consistent with `N`, and Step 1 says `w` is not omitted. This is a contradiction.
- If `P` is empty, `w` is constant, and item 2 applies. So `P` is nonempty and meets `Σ(G)`.

Hence some `f, f'` have `w(f) ≠ w(f')` and `p = f^(-1) f' ∈ Σ(G)`, with `p ≠ 1`.

**Step 3. Finite residual.** A finite quotient is sofic, so every finite-index normal subgroup contains `Σ(G)`.
Every finite-index subgroup `H` contains its normal core, which has finite index. So `Σ(G) ⊆ K(G)`.
- `K(G)` is normal, since conjugation permutes the finite-index subgroups.
- So `f' f^(-1) = f p f^(-1) ∈ K(G)`. It lies in `F F^(-1)` and is not `1`.
- For any finite-index `H`, `f' f^(-1) ∈ H`, so `Hf' = Hf`. No finite-index subgroup puts the points of `F` in
  distinct right cosets.

## Item 4. Transfer

Item 4 of `separated-omitted-patterns-cofinite-proof` shows that the transferred `τ̃` over `G'` is injective and
omits `w` on `F̃`. It says: "Hence `τ̃` is strict over `G_L` on `k` letters and omits `w ∈ A^F̃`." Items 1 to 3
apply to `τ̃` over `G'`.

## What fails for the w11 hypotheses

- Item 1 of `separated-omitted-patterns-make-nonsurjunctive-sizes-cofinite` assumes an omitted letter. Item 2
  above excludes it.
- Its items 2 and 3 assume an omitted pattern with `F F^(-1) ∩ K(G) = {1}`. Step 3 excludes it.
- Its item 4 assumes the same condition in some `G_L`. Item 4 above excludes it.
- Its "Upset" step uses that no pair of `R(τ)` ends at `b`. By item 2, `b^G = τ(c^G)` for some letter `c`, so
  `(c, b) ∈ R(τ)`. That step never applies.
