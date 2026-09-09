---
rg: 2
id: backward-orbit-compressor-modification-proof
kind: route
title: Transpose the compressor's backward orbit to manufacture the two fixed points inside the action
target: compression-action-theorem-for-finitary-linear-extensions
requires:
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

Section 1 of the artifact. Since `uLu^-1 <= L` gives
`u^-1 X^L` inside `X^L`, every `x_i = u^i x` with `i <= 0` is
`L`-fixed. They are distinct: `x = u^-m x` with `m > 0` would put
`ux = u^(1-m)x` in `X^L`, against (1). So
`p = (x_(-1) x_(-2))(x_(-3) x_(-4))` is a finitary permutation matrix
centralizing `L`, and `v = up` satisfies `vLv^-1 = uLu^-1 <= L`,
`va = a`, `vb = b`, `vx = ux` for `a = x_(-1)`, `b = x_(-3)`.

Put `c = T_(xb)`, `y = T_(a,ux)`, `z = T_(ab)`,
`H = <L,v,c,y>`. Then `c` centralizes `L`, and with `ell` in `L`
moving `ux`,

```text
d = [v c v^-1, ell] = T_(ux,b) T_(ell ux, b)^-1,      [y,d] = z.
```

Writing `A = E_(a,ux)` and `B = E_(ux,b) + E_(ell ux, b)`, the four
products `A^2, B^2, BA` vanish and `AB = E_(ab)`, with every
length-three product zero, so `[y,d] = I + AB = z` in characteristic
two. All indices are distinct because `ux` and `ell ux` are not
`L`-fixed while `a` and `b` are.

`d` is a defect generator of `(L,v,c)` in `H`, and `D_H(L)` is
normal, so `z` is in `D_H(L)`. `z` commutes with `L` and `v`
because `a,b` are fixed by both, and with `c` and `y` because the
relevant matrix-unit products vanish in both orders; and `z^2 = I`. So
`<z>` is a nontrivial finite central subgroup of `H` inside
`D_H(L)`. A finite group has property (T) -- average a unit vector
displaced by less than one -- so the prerequisite applies **to `H`**
and kills `z`; restricting any homomorphism from `G` to an MF group
gives the same. Finitary permutation matrices conjugate `z` to every
transvection, and those generate `K` because Gaussian elimination over
`F_2` needs only row additions and swaps, a swap being three additions.

So every MF homomorphism factors through `pi`, giving the radical
identity. For the defect identity, `pi` is the identity on `L` and
carries compressors to compressors and `C_G(L)` into `C_V(L)`, so
`pi(D_G(L)) <= D_V(L)`; the canonical copy of `V` gives the reverse;
and `K = ker pi` lies in `D_G(L)` by the paragraph above.

Residual finiteness of `V` forces `D_V(L) = 1`, because in a finite
quotient the images of `L` and `vLv^-1 <= L` have equal cardinality so
the inclusion is equality and the conjugated centralizer still
centralizes; and it forces `Rad_MF(V) = 1`, because regular
representations of separating finite quotients are MF models in which a
detected element sits at operator distance at least `sqrt 2` from the
identity.
