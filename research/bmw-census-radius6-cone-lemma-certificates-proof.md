---
rg: 2
id: bmw-census-radius6-cone-lemma-certificates-proof
kind: route
title: Proof by the soundness of cone-lemma derivations over the unique BMW normal form, and an exact check of every certificate
target: bmw-census-radius6-cone-lemma-certificates
requires: []
artifacts:
  - experiments/bmw-short4-cone-trees-2026-09-18/certs.jsonl.gz
  - experiments/bmw-short4-cone-trees-2026-09-18/verify_lemmas.py
  - experiments/bmw-short4-cone-trees-2026-09-18/verify_certs.log
  - experiments/bmw-short4-cone-trees-2026-09-18/mutate_lemmas.py
  - experiments/bmw-short4-cone-trees-2026-09-18/mutate_lemmas.log
  - experiments/bmw-short4-cone-trees-2026-09-18/coverage.py
  - experiments/bmw-short4-cone-trees-2026-09-18/coverage.log
---

# Proof

## 1. Normal forms

This is as in §1 of `bmw-census-survivor-cone-tree-certificates-proof`, and `verify_lemmas.py` uses
the same code as `verify_cone.py`.
- It checks both critical-pair families and that `iA` and `iB` are involutions, for the class, before
  it reads the certificate.
- Two words are equal in `Γ` if and only if their normal forms agree.
- `Γ^+` is the set of elements whose normal form has even v-count and even h-count.

`verify_lemmas.py` asserts that every entry of the certificate's word table `els` has a normal form
that is nonempty and in `Γ^+`. So every element named below lies in `Γ^+ − {1}`.

## 2. Certificates and soundness

Suppose `Γ^+` has a left order, with positive cone `P`. Then `P P ⊆ P` and `Γ^+ = P ⊔ P^{-1} ⊔ {1}`.

A certificate is a list of lemmas `L_0, …, L_N`. Lemma `L_i` names a finite set `S_i` and claims
"`S_i ⊄ P`". We prove each claim by induction on `i`, so assume it for every `j < i`.

Suppose `S_i ⊆ P`, and put `Q = S_i`. Each step adds one element `z`, keeping the invariant `Q ⊆ P`:
- **`[z, u, w]`**, with `u, w ∈ Q` and `nf(u w) = nf(z)`. Then `z = u w ∈ P P ⊆ P`.
- **`["sq", z, u]`**, with `u ∈ Q` and `nf(z z) = nf(u)`. Here `z ∈ Γ^+ − {1}`, so `z ∈ P` or
  `z^{-1} ∈ P`. In the second case `u^{-1} = z^{-1} z^{-1} ∈ P`, which contradicts `u ∈ P`. So `z ∈ P`.
- **`["L", j, z]`**, with `j < i` and exactly one element `s` of `S_j` outside `Q`, and
  `nf(s^{-1}) = nf(z)`. If `s ∈ P` then `S_j ⊆ P`, which contradicts lemma `j`. So `s ∉ P`, and
  since `s ∈ Γ^+ − {1}`, `z = s^{-1} ∈ P`.

The proof then ends in one of two ways:
- **`[x, y]`**, with `x, y ∈ Q` and `nf(x y) = ()`. Then `x ∈ P` and `x^{-1} = y ∈ P`, which
  contradicts `P ∩ P^{-1} = ∅`.
- **`["L", j]`**, with `j < i` and `S_j ⊆ Q ⊆ P`. This contradicts lemma `j`.

So `S_i ⊄ P`, for every positive cone `P`. The last lemma has `S_N = ∅`, and `∅ ⊄ P` is false. So
no positive cone exists, and `Γ^+` is not left-orderable.

The radius and the short bound play no role in soundness. They only bound the words the search used.

## 3. The check

`verify_lemmas.py certs.jsonl.gz` checks each record against `census_<pattern>.json`: the normal
form, the critical pairs, the word table, and every step and end of every lemma, in order. It also
checks that the last lemma is empty.
- **Result.** `verify_certs.log` ends with `summary: 509 certificates OK, 0 failed`.
- **Coverage.** `coverage.log` shows that these 509 classes and the 485 of `trees.jsonl.gz` are
  disjoint and together equal `remaining.json`.
- **Non-vacuity.** `mutate_lemmas.log` shows that the checker rejects six corruptions of a valid
  certificate:
  - a dropped step;
  - a wrong product;
  - an end without a contradiction;
  - a nonempty last lemma;
  - a table entry outside `Γ^+`;
  - a lemma step citing its own lemma.

The certificates were translated from LRAT refutations (Glucose 4, then drat-trim) of the radius-6,
short-4 positive-cone CNF by `lrat2cone.py`. That translation is not part of the proof: the checker
re-derives every step in group language.
