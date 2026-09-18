---
rg: 2
id: z2-free-z-normal-form-boundary-has-corner-singular-orbits
kind: claim
title: On its free-product normal-form boundary, Z^2 * Z acts by state-preserving prefix replacements except at four corners, where the germ group is Z^2 over a Z of prefix-replacement germs
distinct_from:
  z2-free-z-embeds-in-a-finite-nucleus-rsg: that asks whether Z^2 * Z embeds in a rational similarity group with finite nucleus, where rational fixed points of Z^2 cannot carry faithful rank-2 germs; this exhibits an action where Z^2 does carry faithful rank-2 germs, at four points only.
  finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs: that is the rank-one germ lemma for finite-nucleus RSGs; this is the calibration showing that a flat produces exactly the germ-group shape that the Belk--Hyde--Matucci finiteness theorem accepts.
  z2-free-z-lies-in-an-fp-full-germ-extension-of-v: that is the finitely presented host built from this action by recoding into V; this is the local computation it uses.
  automatic-groups-embed-in-corner-germ-extensions: that is the OPEN premise for all automatic groups; this is its first worked instance.
artifacts:
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

**ESTABLISHED** (lane proof, elementary, not independently reviewed; no priority claimed).
*Corrected 2026-09-18 (second landing):* the first version's replacement table named several
cylinders wrongly, pairing prefixes that end in different states. The corrected table is below.
The conclusions are unchanged.

## Setting

- **Z^2.** Belk--Bleak--Chatterji--Matucci--Perego, *Rational embeddings of continuous
  automatic groups* (preliminary version, 2026, read at source), Example 1.1(2): on
  `Z^2 = <x, y>` the language `L_2` of words `(ab)^m a^n` and `(ab)^m b^n`, with
  `a ∈ {x, X}`, `b ∈ {y, Y}` (`X = x^-1`, `Y = y^-1`) and `m, n >= 0`, is a continuous normal
  form. Explicitly, `(p, q)` has normal form `(ab)^|q| a^(|p|-|q|)` if `|p| >= |q|`, and
  `(ab)^|p| b^(|q|-|p|)` otherwise, with `a = x^sgn(p)` and `b = y^sgn(q)`.
- **The product.** `G = Z^2 * <t>`, `T = t^-1`, with generating set `x, X, y, Y, t, T`. `L` is
  the set of reduced alternating products of syllables: nontrivial `L_2`-words and `t^k` with
  `k != 0`.

## The automaton

`Pref(L)` is recognized by the deterministic automaton `𝒜` with initial state `q0` and 16
further states. Here `a ∈ {x, X}` and `b ∈ {y, Y}`, and every state except `q0` and `Q_t`, `Q_T`
also has the edges `t -> Q_t` and `T -> Q_T`.

| state | meaning (after reading ...) | other edges |
|---|---|---|
| `q0` | nothing | `x -> A_x`, `X -> A_X`, `y -> P_y`, `Y -> P_Y`, `t -> Q_t`, `T -> Q_T` |
| `Q_t`, `Q_T` | `t^k`, `T^k` (k >= 1) | own loop `t` (resp. `T`); `x -> A_x`, `X -> A_X`, `y -> P_y`, `Y -> P_Y` |
| `A_a` | one letter `a` of a new syllable | `a -> P_a`, `y -> D_ay`, `Y -> D_aY` |
| `P_a` | `(ab)^m a^n`, `n >= 2` | `a -> P_a` |
| `P_b` | `b^n` or `(ab)^m b^n` | `b -> P_b` |
| `D_ab` | `(ab)^m`, `m >= 1` | `a -> E_ab`, `b -> P_b` |
| `E_ab` | `(ab)^m a`, `m >= 1` | `b -> D_ab`, `a -> P_a` |

- Every state has out-degree at least 3, and the 16 states other than `q0` form one strongly
  connected component.
- `∂L`, the accumulation points of `L` in `X^ω`, is the space of infinite paths of `𝒜` from
  `q0`. It is a Cantor space.
- A *state-preserving prefix replacement* is a map `[u] -> [u']`, `uw -> u'w`, where `u, u'` are
  paths from `q0` ending at the same state.

## Statement

1. **Continuity and faithfulness.** `L` is a continuous normal form, and `G` acts faithfully on
   `∂L`.
2. **t is regular.** `t` and `T` act everywhere locally by state-preserving prefix replacements.
3. **Singular points.** `x^±1` and `y^±1` act locally by state-preserving prefix replacements
   at every point except the four *corners* `C = {(ab)^∞}`. Each corner is fixed by all of
   `Z^2`, and at each corner these generators agree with no prefix replacement at all.
4. **Germ groups.** At a corner `c = (ab)^∞`, the germs of `Z^2` form a faithful copy of `Z^2`.
   The germ of the diagonal `δ = (sgn a, sgn b)` is the one-period shift
   `(ab)^M w -> (ab)^(M+1) w`, which is a state-preserving prefix replacement at `D_ab`.

## Proof

- **(1)**
  - Continuity is the criterion of the preprint's Prop. 2.1: `t` changes common-prefix lengths
    by at most one, and a `Z^2` generator only rewrites the first syllable, through the
    continuous action on `L_2 ∪ ∂L_2`.
  - `∂L` has no isolated points, because every boundary point is a limit of infinite
    alternating words.
  - Faithfulness: for `g != 1` with normal form `w`, pick `ξ = (s t)^∞` with a `Z^2`-letter `s`
    chosen so that `w`'s last syllable does not cancel into `ξ`. Then `gξ = wξ != ξ`.
- **(2)** `t` acts by the following maps, with matching end states in each case. `T` is
  symmetric.
  - `[s] -> [ts]` for a `Z^2`-letter `s` (end state `A_a` or `P_b`);
  - `[t^k] -> [t^(k+1)]` for `k >= 1` (`Q_t`);
  - `[Ts] -> [s]` for a `Z^2`-letter `s` (`A_a` or `P_b`);
  - `[T^k] -> [T^(k-1)]` for `k >= 2` (`Q_T`).
- **(3)** Take the generator `x`; the others are symmetric. Every point of `∂L` other than a
  corner has a neighbourhood on which `x` is one of these maps (end states in brackets):

  | point | neighbourhood and replacement |
  |---|---|
  | first letter `t` or `T` | `[t] -> [xt]`, `[T] -> [xT]` (`Q_t`, `Q_T`) |
  | first syllable finite, `= w_(p,q)`, then `t` or `T` | `[w_(p,q) t] -> [w_(p+1,q) t]` (`Q_t`), and likewise with `T`; `[t]` if `(p+1,q) = 0` |
  | `x^∞` | `[x^N] -> [x^(N+1)]`, `N >= 2` (`P_x`) |
  | `X^∞` | `[X^N] -> [X^(N-1)]`, `N >= 3` (`P_X`) |
  | `y^∞`, `Y^∞` | `[b^N] -> [x b^N]`, `N >= 2` (`P_b`) |
  | `(xb)^m x^∞`, `m >= 1` | `[(xb)^m x^N] -> [(xb)^m x^(N+1)]`, `N >= 2` (`P_x`) |
  | `(Xb)^m X^∞`, `m >= 1` | `[(Xb)^m X^N] -> [(Xb)^m X^(N-1)]`, `N >= 3` (`P_X`) |
  | `(xb)^m b^∞`, `m >= 1` | `[(xb)^m b^N] -> [(xb)^(m+1) b^(N-1)]`, `N >= 2` (`P_b`) |
  | `(Xb)^m b^∞`, `m >= 1` | `[(Xb)^m b^N] -> [(Xb)^(m-1) b^(N+1)]`, `N >= 1` (`P_b`) |

  - Each row follows from the normal-form formula for `(p+1, q)`.
  - These cases cover every point of `∂L` except the four corners.
  - At `c = (xy)^∞`: `x` fixes `c`, and it fixes each point `(xy)^M x^∞`, but it moves
    `(xy)^M y^∞` to `(xy)^(M+1) y^∞`. Any prefix replacement defined near `c` that fixes `c` and
    all `(xy)^M x^∞` with `M >= K` is the identity near `c`. So `x` agrees with no prefix
    replacement near `c`. The same holds at the other corners and for `X`, `y`, `Y`.
- **(4)** `(p,q)` sends `(xy)^M y^∞` to `(xy)^(M+p) y^∞` and `(xy)^M x^∞` to `(xy)^(M+q) x^∞`.
  These points accumulate at `c`, so the germ of `(p,q)` at `c` is trivial only if `p = q = 0`.
  The diagonal `xy` maps `[(xy)^M] -> [(xy)^(M+1)]`, with both prefixes ending at `D_xy`. ∎

## The automaton's own Thompson group is not clopen transitive

Let `B_𝒜` be the full group of state-preserving prefix replacements of `∂L`.
- **The invariant.** Sending a clopen set, decomposed into cylinders, to the sum of the end
  states of those cylinders is a well-defined invariant of `B_𝒜`-local equivalence. Its target
  is `K_0 = Z^16 / <s - Σ_{s -> s'} s'>`: refinement respects the relations, and `B_𝒜`-local
  maps match cylinders with equal end states.
- **The computation.** Solving the 16 relations gives `K_0 ≅ Z^5`. The classes of `[t]`
  (`Q_t`) and `[x]` (`A_x`) differ.
- **Consequence.** `B_𝒜` is not clopen transitive, so condition (E5) of
  `automatic-groups-embed-in-corner-germ-extensions` fails for the automaton's own base.
- **The repair.** `z2-free-z-lies-in-an-fp-full-germ-extension-of-v` replaces `B_𝒜` by `V`,
  using `prefix-replacement-actions-recode-into-germ-extensions-of-v`.

## Scope

- `Z^2 * Z` already satisfies Boone--Higman: it is a right-angled Artin group, hence linear.
  The point here is the method.
