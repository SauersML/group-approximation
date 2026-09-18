---
rg: 2
id: one-fp-simple-group-contains-every-s-integral-linear-group
kind: claim
title: For every finite set of primes P, one finitely presented simple group contains GL_n(Z[1/P]) for every n
distinct_from:
  one-fp-simple-group-contains-every-integral-linear-group: that is P empty; this inverts any finite set of primes.
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's theorem, one host per finitely generated subgroup of one GL_n(Q); this is one host for all n at once, for a fixed finite set of primes.
  gl-n-q-embeds-in-fp-simple-group: that is GL_n(Q), which needs all primes at once; this needs only finitely many.
---

**ESTABLISHED** (lane proof, not reviewed; load-bearing, referee review requested) by route
`s-integral-linear-one-host-via-twisted-affine-group`: the host is `D(W_{P,ℓ})` for any prime
`ℓ ∉ P`. It contains every finitely generated `Z[1/P]`-linear group, every `GL_n(O_K[1/P])`
by restriction of scalars, and everything in `DV_F`.

## Toward all primes (`gl-n-q-embeds-in-fp-simple-group`)

Designs of a single "`W_∞`" that were tested against the obstructions on main:
1. **Natural linear action, all primes.** For example, piecewise `GL(Z_(2))`-affine maps of
   `Z_2^D`, which contain the linear `GL_n(Z_(2))` for all odd primes at once. The structure
   group is not finitely generated. No finitely generated host has it: by
   `fg-piecewise-linear-hosts-omit-natural-gl-n-q`, a finitely generated piecewise-affine host
   has linear parts over a finitely generated ring, and no finitely generated commutative ring
   contains `Z_(2)`.
   - *Reason:* a finitely generated `Z`-algebra is a Jacobson ring with finite residue fields.
     All of them would have characteristic 2, so 2 would be nilpotent.
   - The same holds for any `ℓ` and for `A_f`. **Dead.**
2. **Prime-shift twist on one ℓ-adic coordinate.** This transplants the `σ_n` of
   `gl-n-q-lies-in-prime-shift-permutation-group`: one extra homeomorphism `s` with
   `s m_{p_k} s^{-1} = m_{p_{k+1}}`, where `m_p` is multiplication by `p` on a common `ℓ`-adic
   coordinate. **Dead**, and not only inside piecewise-affine groups:
   `no-homeomorphism-shifts-primes-acting-as-l-adic-scalars` shows that no homeomorphism of any
   compact space does this for six primes (`ℓ`-adic six exponentials).
3. **Prime-shift that also moves coordinates** (`p_k` acting on coordinate `d_k`). It survives
   the obstruction in 2, but no intertwiner of `×p_k` and `×p_{k+1}` on `Z_ℓ` is piecewise affine. It
   fixes `0`, so near `0` it would be linear, hence a scalar commuting with `×p_k`. So the host
   leaves the Stein–Farley framework used here. **Open.**
4. **Non-linear embeddings into a fixed `W_{P,ℓ}`.** Is `GL_2(Q)`, or `H_3(Q)`, a subgroup of
   `W = W_{∅,2}`?
   - `W` has roots: every element acting trivially on some coordinate has roots of all orders.
     Cycle `n` bricks of that coordinate and apply the element once per cycle, as in
     Kojima–Sheng for `Q ≤ 2V`.
   - The known obstructions apply only to natural or linear actions, and `W` has no `R^n`-type
     structure for the circle obstructions.
   - **Open**, and the sharpest test is whether `SL_3(Z[1/3])` embeds in `W`: its unipotent must
     then act non-linearly.
