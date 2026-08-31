---
rg: 2
id: depth-mismatched-qutrit-root-bridge-is-residually-finite
kind: claim
title: The first depth-mismatched qutrit root bridge is infinite but residually finite
artifacts:
  - research/depth-mismatched-qutrit-root-bridge-proof.md
distinct_from:
  matched-leavitt-opposite-root-qutrit-bridge-is-gl28: that handles both matched and crossed-zero leaf arrows in one finite prefix chart and obtains GL28; this takes the negative coefficient one level deeper, so no finite chart scalarizes both arrows.
  finite-coefficient-qutrit-root-bridges-are-central-by-finite: the coefficient algebra here is the infinite polynomial algebra F_2[T], not an F_2-finite algebra.
  localized-tail-qutrit-wrappers-reflect-hyperlinearity: that studies off-code actors inside Thompson copies on disjoint leaf tails; these are literal positive-negative elementary roots sharing an external module coordinate.
---

Let `R=L_(F_2)(1,2)`.  Let `D` be a finite maximal binary prefix code,
choose `d_0 in D`, let `a` be a nonempty binary word, and let
`F<=Sym(D)` be finite and transitive in the standard prefix-permutation
copy.  For `n>=2`, set

```text
H=<D_n(F),e_12(s_(d_0)),e_21(t_(d_0 a))> <= EL_n(R).
                                                               (DMQ1)
```

Then, with `m=|D|`, there is an injective chart

```text
H <= GL_(m+1)(F_2[T]),       T |-> t_a,                 (DMQ2)
```

acting trivially on the last `n-2` module coordinates.  The group `H`
is infinite and residually finite, hence sofic and hyperlinear.  The two
displayed opposite roots alone generate the infinite dihedral group
`D_infinity`.

For the qutrit packet take `D=D_27`, `d_0=0`, and `a=0`.  Thus the
first incompatible literal pair

```text
e_12(s_0),       e_21(t_00),       t_00 s_0=t_0         (DMQ3)
```

escapes the finite `GL_28(F_2)` chart but not finite approximation:
the full packet bridge embeds in `GL_28(F_2[T])` and is residually finite.
No finite additive-overlap atlas supported by this subgroup can establish
nonhyperlinearity downstairs in `EL_n(R)`.

For `n>=5`, the corresponding subgroup `Gamma<=St_n(R)` maps onto
`H` with central kernel.  This result does not claim that the restricted
central extension splits or is hyperlinear.  Unlike the finite quotient in
the one-chart theorem, the polynomial quotient does not make `Gamma`
amenable automatically.  The Steinberg-kernel restriction is therefore an
honest remaining seam; the literal subgroup downstairs is completely
closed.
