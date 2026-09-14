---
rg: 2
id: uqs-amenable-extension-closure-proof
kind: route
title: Transplant a forbidden map along a Følner set of the quotient, tile each track, and regroup onto one tile alphabet
target: uqs-groups-are-closed-under-amenable-extensions
requires: []
artifacts:
  - research/artifacts/gk3-approx-surjunctive-2026-09-14.md
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

Artifact Section 3.2 has the full argument. Notation: `Q = G/N`, representatives `s_q` with `s_e = e`,
`s_q g = n_(q,g) s_(q gbar)`, and rows `x_q(n) = x(n s_q)`.

Fix `B` and `w`, and put `delta = delta_G(B,w)`. Suppose `Phi` is an injective automaton from `(B^n x D^j)^G` into
`(Y_1 x ... x Y_n) x (D^(j'))^G`, with memory `M` containing `1`, `(j' - j) log|D| < delta n`, and `Y_i` missing a
pattern `r_i` on `W_i`, `|W_i| <= w`.

1. **Left inverse.** The inverse of `Phi` on its closed image is continuous and equivariant. Extend its local rule to
   get an automaton `sigma` with memory `S` and `sigma Phi = id`.
2. **Følner set.** Choose `eps <= 1/(2w)` with `eps |Sbar| (n log|B| + j log|D|) <= delta n`, and a right Følner set
   `F <= Q` for `Mbar ∪ Sbar ∪ union Wbar_i`. Put `F^+ = F Mbar`, which contains `F`,
   `F^- = {q in F : q Sbar <= F}` and `F'_i = {q in F : q Wbar_i <= F}`. So `|F \ F^-| <= |Sbar| eps |F|` and
   `|F'_i| >= |F|/2`.
3. **Transplant.** By Lemma 2.1 of the transfer artifact, the rows of `Phi(x)` in `F` are an automaton over `N` of
   the rows of `x` in `F^+`. `sigma` recovers the rows in `F^-`. So `Psi(x) = (Phi(x)|_F, x|_(F^+ \ F^-))` is an
   injective automaton over `N`.
4. **Tiles.** A maximal disjoint family `q Wbar_i`, `q in T_i <= F'_i`, has `|T_i| >= |F|/(2w^2)`. Each tile of track
   `i` lies in a proper `N`-subshift over `B^(Wbar_i)` missing a pattern on at most `w` sites: the partial pattern
   `r_i(w)` at coordinates `(wbar, n_(q,w))`, which is consistent since `w -> (wbar, n_(q,w))` is injective.
5. **One alphabet.** Some size `u <= w` carries `n' >= n|F|/(2w^3)` tiles. Put `B' = B^u`. The leftover source and
   target coordinates `E_s`, `E_t` satisfy

   ```text
   log|E_t| - log|E_s| = (j' - j)|F| log|D| + |F \ F^-| (n log|B| + j log|D|)
                        < 2 delta n |F|  <=  delta_N(B', w) n'.
   ```

6. **Normal form.** Take `K` independent copies of `Psi`. Encode `E_t^K` injectively into a power of `E = E_s`, or of
   `B'` if `|E_s| = 1`. The margin is at most `K (log|E_t| - log|E_s|) + log|E|`. For large `K` this is below
   `delta_N(B', w) K n'`, which contradicts UQS of `N`.
