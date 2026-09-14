---
rg: 2
id: two-rectangle-surjunctive-images-kill-all-designs
kind: claim
title: A window whose two-rectangle table group has a surjunctive image separating its reverse products carries no strict design
distinct_from:
  strict-pairs-transfer-to-table-realizations: that pushes one strict pair forward along a realization of its tables and needs a Garden-of-Eden window; this needs no window and no rules, because separating the reverse products decides surjectivity for every design at once.
  small-leavitt-invariant-output-windows-have-finite-separations: that screens only invariant-output designs through a finite image keeping x_h nontrivial; this screens every design on a window, whatever its alphabet and rules.
  strict-automata-live-on-canonical-table-groups: that decides strictness of a fixed design through the canonical group of a minimal forward partition; this fixes a window in an ambient group and excludes all designs on it through one image of the ambient two-rectangle table group.
artifacts:
  - research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md
  - experiments/gk3-leavitt-nonlinear/general_window_screen.py
---

**ESTABLISHED** by `two-rectangle-surjunctive-images-kill-all-designs-proof`.

**Setting.** `G` is a group and `S, M` are finite subsets of `G` containing `1`.
The **two-rectangle table group** of the window `(S, M)` is

```text
T = < x_a (a in S u M), x_1 = 1 |
      x_s x_m = x_s' x_m'   whenever s m = s' m' in G   (s, s' in S; m, m' in M),
      x_m x_s = x_m' x_s'   whenever m s = m' s' in G   (m, m' in M; s, s' in S) >.
```

An element lying in both `S` and `M` has one letter. `x_a -> a` is a homomorphism
`T -> G`.

**Theorem.** Suppose some homomorphism `psi` from `T` into a surjunctive group `K`
satisfies

```text
psi(x_m x_s) = psi(x_m' x_s')   only if   m s = m' s' in G      (m, m' in M; s, s' in S).
```

Take any finite alphabet and any automata `tau` with memory `M` and `sigma` with
memory `S` over `G` with `sigma tau = id`. Then `tau` is surjective. So no design on
`(S, M)` gives a strict pair over `G`.

**Corollaries.**
1. **Sofic images combine.** Suppose that for each pair of `G`-distinct reverse
   products some homomorphism from `T` into a sofic group separates that pair. The
   product homomorphism into the direct product, which is sofic, separates all pairs.
   So a strict pair on `(S, M)` needs one pair with `m s != m' s'` in `G` whose hinge
   word `x_s'^-1 x_m'^-1 x_m x_s` lies in the kernel of every homomorphism from `T`
   into a sofic group. Combining general surjunctive targets the same way would need
   `finite-direct-products-of-surjunctive-groups-are-surjunctive`, which is open.
2. **Localization.** If `<S u M>` is sofic, `x_a -> a` itself is a separating image.
   So the theorem contains the classical exclusion of windows in sofic subgroups.
3. **Freeness.** If every coincidence in both rectangles holds already in the free
   group on the letters, `T` is free and hence residually finite. Its finite images
   separate the finitely many distinct reverse products, so the window is dead.

**Use.** This is a rule-free filter for all designs on a window of a fixed ambient
group, in particular over `L_(F_2)(1,2)^x`. It needs one image of `T` and no
Garden-of-Eden pattern. `experiments/gk3-leavitt-nonlinear/general_window_screen.py`
emits GAP searches for such images with replayable permutation witnesses.

**Relation to earlier results.** The proof is Lemmas 2 and 3 of
`research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md`
applied to the realization through `psi`. No priority is claimed.
