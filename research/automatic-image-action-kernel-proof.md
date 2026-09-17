---
rg: 2
id: automatic-image-action-kernel-proof
kind: route
title: Build the graph of a word as a composite of synchronous rational relations and test its inclusion in the regular point equality by automaton emptiness
target: automatic-image-actions-have-recursive-kernels
requires: []
---

Notation as in `automatic-image-actions-have-recursive-kernels`. All constructions
below are effective on finite automata.

**Valid convolutions.** Let `C_r` be the set of words over `(Σ ∪ {⋄})^r` such that
each track lies in `Σ* ⋄*` and no column is `(⋄, ..., ⋄)`. `C_r` is regular, and
`(x_1, ..., x_r) -> x_1 ⊗ ... ⊗ x_r` is a bijection `(Σ*)^r -> C_r`. Thus a
synchronous rational `R` corresponds to a regular `L_R ⊆ C_r`.

**(P1) Boolean operations.** `R ∩ R'`, `R ∪ R'` and the complement `(Σ*)^r \ R`
are synchronous rational: use `L_R ∩ L_R'`, `L_R ∪ L_R'`, `C_r \ L_R`.

**(P2) Permuting and adding tracks.** Permuting tracks is a letter-to-letter
morphism mapping `C_r` to itself, so it preserves regularity. Adding a track: let
`h : (Σ ∪ {⋄})^(r+1) -> (Σ ∪ {⋄})^r` delete the last coordinate of each column. For
`x ⊗ z` in `C_(r+1)`, `h(x ⊗ z)` equals the `r`-track convolution of `x` followed by
some columns `(⋄, ..., ⋄)`. Hence
`{x ⊗ z : x ∈ R} = C_(r+1) ∩ h^(-1)(L_R (⋄, ..., ⋄)*)`, which is regular.

**(P3) Deleting a track.** Let `R ⊆ (Σ*)^(r+1)`, and let `R'` be its projection to
the first `r` tracks. With `h` as in (P2), `h(L_R)` is regular and consists of the
words `x ⊗ ... ` of `R'` followed by padding columns `(⋄, ..., ⋄)^k`. So
`L_(R') = C_r ∩ (h(L_R) / (⋄, ..., ⋄)*)`. Here `/` is the right quotient, whose
automaton is that of `h(L_R)` with final states replaced by the states from which
some `(⋄, ..., ⋄)^k` reaches a final state. It is regular, and effective.

**(P4) Composition and inverse.** For binary `R, R'`, set
`R ∘ R' = {(x, z) : ∃y (x, y) ∈ R', (y, z) ∈ R}`. Add a track to each, intersect by
(P1) and (P2), then delete the middle track by (P3). The inverse of `R` is obtained
by swapping the tracks.

**The graph of a word.** For `w = g_(i_1)^(e_1) ... g_(i_k)^(e_k)`, define
`E_w = E_(i_1)^(e_1) ∘ ... ∘ E_(i_k)^(e_k)`, where `E^(-1)` is the inverse relation
and `E^(1) = E`; set `E_(empty word) = ~`.

*Claim.* `(x, y) ∈ E_w` implies `ν(y) = w ν(x)`, and every `x ∈ L` has some `y`
with `(x, y) ∈ E_w`.

*Proof.* By induction on `k`. For a single letter with `e = 1`, both hold by
definition. For `e = -1`: `(x, y) ∈ E_i^(-1)` means `ν(x) = g_i ν(y)`, so
`ν(y) = g_i^(-1) ν(x)`. For totality, let `s = g_i^(-1) ν(x)` and pick `y_0 ∈ L`
with `ν(y_0) = s`, possible since `ν` is onto. Since `E_i` has domain `L`, some
`(y_0, x') ∈ E_i` exists, and then `ν(x') = g_i s = ν(x)`. Composition preserves
both properties. `∎`

**Decision procedure.** `w` acts trivially iff `ν(y) = ν(x)` for all
`(x, y) ∈ E_w`, that is, iff `E_w ⊆ ~`.
- If `w` acts trivially, every `(x, y) ∈ E_w` has `ν(y) = w ν(x) = ν(x)`, so
  `x ~ y`.
- Conversely, suppose `E_w ⊆ ~`. For `s ∈ S`, pick `x` with `ν(x) = s` and `y` with
  `(x, y) ∈ E_w`, by totality. Then `w s = ν(y) = ν(x) = s`.

`E_w ⊆ ~` iff the regular language `L_(E_w) ∩ (C_2 \ L_~)` is empty, which is
decidable. The automata for `E_w` are computed from `w` by (P1)-(P4). `∎`

**Examples (Consequence 3).** Let `L = {0,1}*`, `ν(u) = u 0^ω`, and let
`u ~ v` iff the longer of `u, v` is the shorter followed by zeros. Then `~` is
synchronous rational: check column by column that the letters agree, or that the
unpadded letter is `0`.

Let `g` be given by a complete prefix code `u_1, ..., u_p` and targets `v_j`, with
`|v_j| - |u_j|` in `[-d, d]`. Put `E_g = {(u_j t, v_j t) : j, t} ∘ ~` and include
`~` on the right as well. Since `~ ∘ E ∘ ~` is synchronous rational by (P4), it is
enough that `{(u_j t, v_j t) : t}` is. An automaton reads `u_j ⊗ v_j` and then
compares the two tracks with a buffer of the last `d` letters.

Every word `x` is `~`-equivalent to a word extending some `u_j`, by appending
zeros, so `E_g` has domain `L`. The same bounded-buffer argument covers the other
tail-class and Houghton examples.
