---
rg: 2
id: alphabet-enlarging-covers-refute-dual-and-domain-duality
kind: claim
title: A strongly post-surjective automaton onto a larger full shift refutes dual surjunctivity, CP and PSD at its group, and has no right inverse
distinct_from:
  post-surjective-automata-never-enlarge-the-alphabet: that is the open non-existence statement NPE; this proves what a counterexample to it would refute and why no counterexample can come from a strict pair.
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that turns a strict pair with a post-surjective decoder into a dual failure that has a right inverse; this turns an alphabet-enlarging cover into dual and proper-domain failures that have none.
  cover-pair-sections-force-fixed-point-surjectivity: that proves sections force D = ∅ for any cover pair; this exhibits the natural family of cover pairs with D ≠ ∅ and shows it is governed by a two-alphabet rank statement.
  full-shifts-with-different-alphabets-are-not-conjugate: that counts constants to forbid alphabet-shrinking injections; this uses that count only in part 4.
  linear-proper-domain-duality-is-stable-finiteness: that shows linear PSD failures exist exactly off stable finiteness; this shows linear alphabet-enlarging covers never exist, so those linear failures never factor through NPE.
---

**ESTABLISHED 2026-09-18** by [[alphabet-enlarging-covers-refute-dual-and-domain-duality-proof]]. Elementary.

Let `G` be any group, `A ⊊ B` finite alphabets, and `P : A^G → B^G` an automaton that is strongly
post-surjective with constant `Φ` (definition in `strict-pairs-give-dual-failures-on-bounded-defect-domains`).
Such a `P` is a counterexample to `post-surjective-automata-never-enlarge-the-alphabet` at `G`. Then:

1. **Dual surjunctivity fails.** For any onto letter map `q : B → A`, `F = P ∘ q^G : B^G → B^G` is strongly
   post-surjective (same `Φ`) and not pre-injective. So `every-group-is-dual-surjunctive` fails at `G`. Plain
   post-surjectivity of `P` already suffices here.
2. **CP fails.** `X = A^G ⊊ B^G` is an SFT containing constants, and `P : X → B^G` is strongly post-surjective
   with lifts in `X`. So `constant-point-sft-domains-admit-no-post-surjective-covers` fails at `G`.
3. **PSD fails.** Let `C = B × B` and `C' ⊊ C` with `|C'| = |A|^2 + 1`. For an onto non-injective letter map
   `s : C' → A × A`, `F' = (P × P) ∘ s^G : C'^G → C^G` is strongly post-surjective with lifts in `C'^G`, and
   not pre-injective. `C'^G ⊊ C^G` is a strongly irreducible SFT. So
   `proper-sft-domains-admit-no-dual-failures` fails at `G`.
4. **No right inverse, deficiency.** `P` maps the `|A|` constants of `A^G` onto at most `|A|` constants of
   `B^G`, so `D(A^G, P) ≠ ∅`. There is no equivariant map `R : B^G → A^G` with `P ∘ R = id`, continuous or
   not. The same holds for `F` in part 1, for the pair in part 2 and for `F'` in part 3. So none of these
   failures has a section or an automaton right inverse.
5. **Linear sector.** If `A = F^m`, `B = F^n` for a finite field `F` and `P` is `F`-linear, then `n ≤ m`. So a
   linear `P` as above never exists, over any group.

**What this changes.**
- `every-group-is-dual-surjunctive`, CP and PSD each imply NPE at the same group. NPE is a rank condition that
  holds for linear maps over every group and fails for the free monoid. Over groups it is known only where
  dual surjunctivity is, in particular for sofic groups.
- Every counterexample to any of the three built from an NPE failure is fixed-point deficient. By
  `cover-pair-sections-force-fixed-point-surjectivity` and Corollary F3 of its artifact, the Gottschalk routes
  never consume such pairs. So proving CP or PSD for all groups includes proving NPE, which is not known to
  follow from surjunctivity.
- If `post-surjective-automata-admit-automaton-right-inverses` holds at `G`, then with
  `post-surjective-decoders-convert-strict-pairs-to-dual-failures` an NPE failure at `G` makes `G`
  non-surjunctive. So that claim must, in particular, manufacture a right inverse from a failure that has none
  and cannot acquire one (part 4). This is where it has to do real work.
- The host-change attempt on `dual-surjunctive-groups-are-surjunctive` (Attempts, 2026-09-18) is dead, and this
  is its by-product.
