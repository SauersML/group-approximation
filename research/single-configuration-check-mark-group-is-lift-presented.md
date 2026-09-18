---
rg: 2
id: single-configuration-check-mark-group-is-lift-presented
kind: claim
title: The one-configuration layer of the Wächter–Weiß check-mark automaton is non-contracting and of exponential activity, yet its relator kernel is the lift ideal of two commutators, so its V_3 is finitely presented
distinct_from:
  polynomial-automata-reduce-to-cycling-relators: that criterion needs (P1), which fails here because the continue state N loops at both digits (exponential activity); this is proved with the path-by-path criterion instead.
  linear-activity-odometer-automaton-has-fp-nekrashevych-group: that is a linear-activity example with N = K_∞; this is an exponential-activity example whose relator kernel needs two genuine relators, since both are fixed by the section map along 0^ω.
  finite-commutator-wachter-weiss-groups-are-not-fp: that reduces the Wächter–Weiß question to the full check-mark group C; this settles its first layer (one configuration, no # or $) and isolates what the configuration layer adds.
---

**ESTABLISHED** by `single-configuration-check-mark-group-is-lift-presented-proof` (lane proof by
bh-free-02, elementary, not independently reviewed; no priority claimed).

## The automaton

Alphabet `X = {0, 1, γ}`. Write `g = π(g_0, g_1, g_γ)`, with `σ` swapping `0` and `1` and fixing `γ`:

```text
A = σ(Z, A', 1),   A' = σ(N, A', 1),   Z = (Z, N, 1),   N = (N, N, A).        (CM1)
```

This is the check-mark automaton of Wächter–Weiß (arXiv:1906.03424v3, Figure
`fig:checkmarkingAutomaton`), unencoded, restricted to the sub-alphabet of digits and one symbol
letter `γ`, with continuation `id`.
- `A` is `checksub`, `A'` its carry state, `Z` the state "block zero so far", and `N` "block nonzero,
  continue". The figure's code writes the `Γ`-edge out of state 3 as going to a node `(1)`, which is
  not defined; by the text it is the check-mark state.
- On `{0,1,γ}^*`, the skip state acts trivially, since it acts only at `#`. So `Z|_γ = 1` here.
- `C_2 = ⟨A, A', Z, N⟩` acts on sequences of digit blocks `b_1 γ b_2 γ ⋯` by the cascade: increment
  `b_1`; continue to `b_2` if the old `b_1` was neither `0` nor all ones; and so on.

## Statement

1. **Two relators.** `A' N A'^{-1} = N` and `Z N Z^{-1} = N` in `C_2`.
2. **Lift presentation.** The relator kernel is `N_{C_2} = ⟨⟨[A',N], [Z,N]⟩⟩_lift`. Hence `V_3(C_2)` is
   finitely presented (Theorem A of `rover-nekrashevych-fp-iff-finite-lift-presentation`), and `C_2`
   embeds in a finitely presented simple group (`lift-presented-automaton-groups-satisfy-boone-higman`).
3. **Not covered by earlier criteria.**
   - `C_2` has exponential activity: `N|_0 = N|_1 = N`, so (P1) of
     `polynomial-automata-reduce-to-cycling-relators` fails.
   - `C_2` is not contracting: along `(bγ)^ω` with `b` a long block of middle value, the section
     of `A^n` is `A^n` at every step, while `A` has infinite order.
   - `C_2` contains a copy of `Z ≀ Z`: `A` together with `Z^{-1}N`, the lamp "apply `A` from the next
     block if this block is zero".

## Lesson for general BH

The Wächter–Weiß counter is not what blocks lift-presentation. Its first layer is lift-presented.
- *Where the relators go.* Separators reset every relator to a power of one element, which is
  therefore freely trivial. Inside a block, letter types only decay, so relators stabilize only on
  the constant rays `0^ω` and `1^ω`. There they lie in two small free abelian subgroups, governed by
  two commutators.
- *What this means for PSPACE.* The rung needs lift-presentation only of the layers above:
  - configurations separated by `#`, where the skip state acts;
  - the finite lamp group of the checkers.

  The first is analysed in `research/artifacts/gq-bh-bh-free-02-check-mark-layers.md`. There the skip
  state `K` and the continue state `N` generate a lamplighter `Z ≀ Z` persistent along `0^ω`, and that
  is the precise remaining crux.

DERIVATION
single-configuration-check-mark-group-is-lift-presented-proof
