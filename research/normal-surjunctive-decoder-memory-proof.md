---
rg: 2
id: normal-surjunctive-decoder-memory-proof
kind: route
title: Transplant the automaton to the kernel along coset coordinates and contradict surjunctivity of the kernel
target: normal-surjunctive-decoder-memory-forces-surjectivity
requires: []
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

Section 2 of the artifact.

1. **Coordinates.** Put `x_q(n) = x(n s_q)` for representatives `s_q` of `G/N`. Left translation by `N` is the shift
   in every coordinate. The encoder reads coordinates `q mbar` at `N`-offsets `n_(q,m) = s_q m s_(q mbar)^-1`
   (Lemma 2.1).
2. **The decoder stays on its coset.** Its memory lies in `N`, so `s_q d s_q^-1 in N` and it acts coordinatewise.
3. **Transplant.** A Garden of Eden pattern `p` on `W` gives `F = Wbar` and `F^+ = F Mbar`. The map
   `x -> (tau_F(x), x|_(F^+ \ F))` is an injective automaton over `N` between full shifts of equal alphabet size.
4. **Proper image.** Its image lies in the proper subshift avoiding the transported pattern at every `N`-offset.
   So it is not surjective, contradicting surjunctivity of `N`.

No amenability of the quotient or of any memory group is used.
