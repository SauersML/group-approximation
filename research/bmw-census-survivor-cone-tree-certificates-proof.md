---
rg: 2
id: bmw-census-survivor-cone-tree-certificates-proof
kind: route
title: Proof by the soundness of cone-propagation trees over the unique BMW normal form, and an exact check of every packed tree
target: bmw-census-survivor-cone-tree-certificates
requires: []
artifacts:
  - experiments/bmw-cone-trees-2026-09-18/trees.jsonl.gz
  - experiments/bmw-cone-trees-2026-09-18/verify_cone.py
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.py
  - experiments/bmw-cone-trees-2026-09-18/verify_trees.log
  - experiments/bmw-cone-trees-2026-09-18/mutate_test.py
  - experiments/bmw-cone-trees-2026-09-18/mutate_test.log
---

# Proof

## 1. Normal forms

Fix a class. `Γ` is presented by:
- the h-letters `A` and the v-letters `B`;
- `x · iA(x) = 1` and `y · iB(y) = 1`;
- the `m n` squares `h v = v' h'`, one for each pair `(h, v)`.

Take the rewriting system `h v → v' h'`, `x iA(x) → 1`, `y iB(y) → 1`.
- **Termination.** Each rule either shortens the word or keeps its length and lowers the number of
  pairs (h-letter before v-letter).
- **Confluence.** The only overlaps are `iA(h) h | h v` and `h v | v iB(v)`. `verify_cone.py`
  resolves both for every `h` and `v` of the class before it reads the tree. It also asserts that
  `iA` and `iB` are involutions.

By Newman's lemma the system is confluent. Every rule is a relation of `Γ`, and conversely every
relator reduces to the empty word, so two words are equal in `Γ` if and only if they have the same
normal form. The normal form is a reduced v-word followed by a reduced h-word.

The parity kernel `Γ^+` is the set of elements whose normal form has an even number of v-letters and
an even number of h-letters. This is well defined, since every rule preserves both parities mod 2.
`verify_cone.py` tests membership as `inK`.

## 2. Certificates and soundness

A certificate is a binary tree whose nodes are of two kinds.
- **Split.** `["split", g, T_1, T_2]` requires `g ∈ Γ^+` and `nf(g) ≠ ()`. The branch `T_1` adds
  `g` to the assumed set, and `T_2` adds `g^{-1}`.
- **Leaf.** `["leaf", [x, y], steps]`. Each step `[z, u, w]` requires:
  - `nf(u)` and `nf(w)` are in the current set, meaning assumed on the path or derived earlier in the
    same leaf;
  - `nf(z) = nf(u w)`, `z ∈ Γ^+` and `nf(z) ≠ ()`.

  The step then adds `nf(z)`. At the end, the leaf requires `nf(x)` and `nf(y)` in the set and
  `nf(x y) = ()`.

Suppose `Γ^+` has a left order, with positive cone `P`. Then `P P ⊆ P` and `Γ^+ = P ⊔ P^{-1} ⊔ {1}`.
Descend the tree while keeping the invariant "every assumed element lies in `P`".
- **At a split.** `g ≠ 1` by §1, so `g ∈ P` or `g^{-1} ∈ P`. One of the branches keeps the invariant.
- **At a leaf.** Every derived `z` equals `u w` in `Γ` (§1), with `u, w ∈ P`, so `z ∈ P`. Finally
  `x, y ∈ P` and `y = x^{-1}`, which contradicts `P ∩ P^{-1} = ∅`.

So `Γ^+` has no left order. The radius `R` plays no role in soundness. It only bounds the words the
search used.

## 3. The check

`verify_trees.py trees.jsonl.gz` runs `verify_cone.py` on each record `(pattern, class, tree)` against
`census_<pattern>.json`. `verify_trees.log` has one line per class and ends with
`summary: 485 certificates OK, 0 failed`.

`mutate_test.log` shows that the checker is not vacuous. It rejects four corruptions of a valid
certificate:
- a dropped step;
- a wrong product;
- a leaf without a contradiction;
- a split on an element outside `Γ^+`.

The trees were found by `dtree2.py`, a lookahead DPLL search over cone propagation in the radius-`R`
ball. That search is not part of the proof.
