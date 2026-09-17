---
rg: 2
id: data-routed-transport-universality-proof
kind: route
title: Transpose the output into the identity address, count weights on Klein cosets, and match hypercube edges
target: data-routed-automata-defeat-transport-accounting
requires:
  - binary-three-address-strict-automata-are-linear
---

## Parts 1 and 2: presentations exist

**Part 1.** Put `s(p) = 1`. Let `pi(p)` be the transposition of `p(1)` and `f(p)` when they differ, and
the identity otherwise. Then `pi(p)(p(s(p))) = f(p)` for every pattern `p`.

**Part 2.** Let `A = {0,1}`. A copy presentation with memory `M` needs, for each pattern `p`, an address
`j` with `p(j) = f(p)`. Such an address fails to exist only when `p` is constant and `f(p)` is the other
letter, that is, when `tau` does not fix that constant configuration.

If `tau` is injective:
- a constant configuration is fixed by all translations, so its image is too, and hence it is constant;
- `tau` is therefore an injective map of the two constants to themselves, so it permutes them;
- if it swaps them, the composite `tau` followed by the letter swap `x -> 1 + x` fixes both constants;
- the letter swap is a reversible automaton, so injectivity and surjectivity are unaffected.

## Part 3(a): the Klein parity involution

**Bijectivity.** `L` is right multiplication by `u = 1 + a + b` in `F_2[G]` acting on `F_2^G`.
Since `V` is abelian with `a^2 = b^2 = 1`, we get `u^2 = 1 + a^2 + b^2 = 1` over `F_2`, so `L o L = id`.

**Reduction to one coset.** Take a copy presentation `s` with memory `M = {1, a, b}`, so that
`r_x(g) = g s(p_g)` lies in `gV`. Then:
- reads never leave left cosets of `V`, and the pattern `p_g` depends only on `x` restricted to `gV`;
- so `N_x(1)` depends only on `x` restricted to `V`;
- the presentation is equivariant and `mu` is translation invariant, so `mu{N_x(h) = 0}` is the same for
  every `h`;
- hence `mu{N = 0} = E(U)/4`, where `U` is the number of unread sites of `V` under `x` restricted to `V`.

**Allowed addresses.** The output at `g` is the parity of `p_g`. So a pattern of weight 1 must read its
unique 1-coordinate, and a pattern of weight 2 must read its unique 0-coordinate. Patterns of weight 0 or 3
may read any address. Let `w` be the weight of `x` on `V` (probability `C(4,w)/16`), and let `y = L(x)`.

- **`w = 0` or `w = 4`.** Every site sees the same constant pattern, so `s` is one address `m`, and `r_x`
  is right translation by `m`. So `U = 0`.
- **`w = 1`, `x = delta_h`.** `y` is the indicator of `{h, ha, hb}`. Since `y = x o r_x` and `x` has a single
  1 at `h`, the three sites `h, ha, hb` read `h`, and `hab` reads a 0-site. So the image has two sites and
  `U = 2`.
- **`w = 3`, `x = 1 + delta_h`.** `L(1) = 1` on `V`, so `y` is the indicator of `{hab}`. The three sites
  `h, ha, hb` read `h`, and `hab` reads one 1-site. So `U = 2`.
- **`w = 2`, `x = delta_h + delta_(hc)`.** Each pattern `p_g` sees `V` minus `{g ab}`, so it has weight 1
  or 2, and `s` is forced.
  - For `c = a`: `h` and `ha` see weight 2 and read `b`, while `hb` and `hab` see weight 1 and read `b`.
    So `r_x = (h -> hb, ha -> hab, hb -> h, hab -> ha)`, which is bijective.
  - `c = b` is the same with `a` and `b` exchanged.
  - For `c = ab`: `h` and `hab` see weight 1 with the 1 at address `1`, and `ha` and `hb` see weight 2 with
    the 0 at address `1`. So `r_x` is the identity.

  So `U = 0`.

Hence `E(U) = 2 (4 + 4)/16 = 1`, and `mu{N = 0} = 1/4` for every copy presentation with memory `M`. The
script confirms this by enumerating all 9 presentations on `V` itself.

## Part 3(b): the order-three multiplexer

Reads stay in left cosets of `<t>`. Write a coset configuration as `(x(g), x(gt), x(gt^2))`. Site `i`
reads `i` when site `i - 1` is 0, and `i + 1` otherwise (indices mod 3). The eight configurations, with
their outputs, read maps and unread counts, are:

| x | y | reads | unread |
|---|---|---|---|
| 000 | 000 | 0,1,2 | 0 |
| 100 | 100 | 0,2,2 | 1 |
| 010 | 010 | 0,1,0 | 1 |
| 110 | 101 | 0,2,0 | 1 |
| 001 | 001 | 1,1,2 | 1 |
| 101 | 011 | 1,2,2 | 1 |
| 011 | 110 | 1,1,0 | 1 |
| 111 | 111 | 1,2,0 | 0 |

The outputs are pairwise distinct, so the rule is bijective on every coset, and hence on `{0,1}^G`.

**Blindness.** The selection depends only on `x(g t^-1)`, and the selected address is `1` or `t`, never
`t^-1`.

**Densities.** The average unread count is 6/24 per site, so `mu{N = 0} = 1/4` by the same coset reduction.
Also `E N = 1`, since the three sites of a coset make three reads inside it. So
`E (N - 1)_+ = E N - 1 + mu{N = 0} = 1/4`.

## Part 4: blind copy rules and hypercube matchings

Identify `A^M` with the cube `{0,1}^n`, and write `p + e_m` for `p` flipped at address `m`.

**From presentations to matchings.** Let `s` be a blind copy presentation and put
`iota(p) = p + e_(s(p))`. Blindness gives `s(iota(p)) = s(p)`, so `iota(iota(p)) = p`, and `iota` has no
fixed points. So `iota` is a perfect matching of the cube in which each edge is labelled by its direction
`s(p)`, and `f(p) = p(s(p))`.

**From matchings to presentations.** Given a perfect matching, let `s(p)` be the direction of the edge at
`p`, and define `f(p) = p(s(p))`. The partner of `p` has the same direction, so `s` is blind.

**Balance.** The two ends of an edge differ exactly at the address read, so their outputs are 0 and 1.
Since the edges partition the cube, `f` is balanced.

**No linear rule of support at least two is blind.** Let `f = epsilon + sum_(m in S) p(m)` with `|S| >= 2`,
and suppose a blind copy presentation exists.
- **Reads stay in `S`.** If `s(p) = m` is outside `S`, then `f(p + e_m) = f(p)`, but the two ends of an
  edge have different outputs. So `s(p) in S` always.
- **`epsilon = 1`.** The zero pattern has `f = 1` and no coordinate equal to 1, so no copy presentation
  exists at all.
- **`epsilon = 0`.** For `m in S` the pattern `e_m` has `f = 1`, and its only 1-coordinate is `m`, so
  `iota(e_m) = 0`. Since `|S| >= 2`, two different patterns are matched to `0`, which contradicts that
  `iota` is an involution.

The script confirms these facts by exhaustion for `n <= 4`.

## Part 5: the corollary

Let `tau` be an injective, non-surjective binary automaton with a blind copy presentation `s` on a memory
`M` with `|M| <= 3`.
- By `binary-three-address-strict-automata-are-linear`, the minimal memory `M_0` of `tau` has three
  elements, and the rule on `M_0` is `epsilon + sum_(m in M_0) x_m`.
- The minimal memory is contained in every memory, so `M_0 = M`.
- The rule is then a linear rule on `M` with support three, and by Part 4 it has no blind copy
  presentation. This is a contradiction.

Hence `tau` is surjective.
