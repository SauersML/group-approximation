---
rg: 2
id: basilica-hnn-fp-infinity-answers-kourovka-21-140
kind: route
title: If the finitely presented Basilica HNN extension is FP_infinity, it is a torsion-free F_infinity group of infinite cd without Thompson's F, answering Kourovka 21.140 and Zaremsky 2.8 with no amenability hypothesis
target: some-torsion-free-f-infinity-group-of-infinite-cd-omits-f
requires:
  - basilica-hnn-extension-is-fp-infinity
  - basilica-hnn-extension-is-fp-amenable-non-ea
  - basilica-group-is-torsion-free-and-contains-every-z-n
  - thompson-f-free-groups-closed-under-extensions-and-unions
---

**Route (conditional on one OPEN premise).** Let `B` be the Basilica group and `B~ = B*_σ` its
Bartholdi–Virág ascending HNN extension along `b ↦ a, a ↦ b^2`.

1. `B~` is finitely presented (`basilica-hnn-extension-is-fp-amenable-non-ea`).
2. `B~` is torsion-free and contains `Z^n` for every `n`, so `cd B~ = ∞`
   (`basilica-group-is-torsion-free-and-contains-every-z-n`, item 5).
3. **`B~` contains no copy of Thompson's `F`, unconditionally.**
   - `B` acts faithfully on the binary rooted tree, so it is residually finite.
   - Then `thompson-f-free-groups-closed-under-extensions-and-unions`, item 5, applies to the ascending HNN
     extension `B*_σ`.
   - No amenability of `F` is used.
4. If `B~` is of type `FP_∞` (`basilica-hnn-extension-is-fp-infinity`, OPEN), then by 1 it is of type `F_∞`. With
   2 and 3 it is a torsion-free `F_∞` group of infinite cohomological dimension without `F`. That is the
   target. ∎

## What it answers

- **Kourovka 21.140** (arXiv:1401.0300v46, S. Witzel and M. C. B. Zaremsky): "Let `G` be a torsion-free group of
  type `F_∞` of infinite cohomological dimension. Must `G` contain a copy of Thompson's group `F`?" The answer
  would be **no**.
- **Zaremsky Problem 2.8** (`zaremsky-2-08-infinite-dim-torsion-free-f-infinity-without-f`) would be solved by
  construction.
- **FFKLZ** (arXiv:2506.02319v2, l.286–293) note that a torsion-free finitely presented witness to their Q2.4
  would answer Witzel's question. This route answers the question without passing through oligomorphic actions.

## Status after this route

- Before this route, main reached the target from `B~` only through `omits-f-from-torsion-free-amenable-non-ea-f-infinity`,
  which also needs `thompson-f-is-not-amenable` (open, and famous).
- Kourovka 21.140 for `B~` is now exactly one finiteness question, `FP_3, FP_4, …` for an explicit
  two-generator, two-relator group: `B~ = ⟨a, t | t^(−2) a t^2 = a^2, [a, a^(t a t^(−1))] = 1⟩`.
- **Constraints on that question are on the crux node:** the Kropholler fence (`FP_∞` forces `B ∉ H𝔉`), the
  degree-3 Alexander-module test, and the sanity constraint that a disproof must use features `F` lacks.
- The completion searches in `experiments/hnn-rewriting-2026-09-17` (a finite complete rewriting system would
  give `F_∞` by Brown's collapsing-scheme theorem, cited and not re-read) have not completed for the Basilica presentations. The Grigorchuk
  analogue is killed for base-first wreath orderings (`grigorchuk-hnn-has-no-base-first-wreath-rewriting-system`).
- **Same argument, other bases.** Every finitely presented ascending HNN extension of a torsion-free weakly
  branch group has infinite cd (a weakly branch group contains `Z^n` for every `n`) and contains no `F` (item 3).
  So any such extension of type `FP_∞` answers 21.140.

## Lesson for general BH

The Thompson-free half of Witzel's question is free for anything built from residually finite pieces by
extensions and ascending HNN extensions. That is exactly how branch groups are made finitely presented. What
remains is a pure finiteness problem, the same kind of problem that stands between the L-presentation of a
branch group and an `F_∞` host. That problem recurs on the BH side for germ and self-similar hosts, where
finite presentation of germ groups is the gate.
