---
rg: 2
id: mf-fails-with-elementary-abelian-kernel
kind: claim
title: MF fails for a split extension with elementary abelian kernel and linear quotient
distinct_from:
  mf-extension-nonclosure: That established claim already gives non-closure under extensions, with the *nonabelian* Clifford lamp kernel `ClLamp(X)` and the quotient `V`; the delta here is that the kernel can be taken elementary abelian of exponent two and the quotient linear over `Q`, so no averaging or induction over an abelian kernel can repair MF.
  mf-not-closed-under-integer-extensions: That shrinks the quotient to `Z` and strengthens the kernel to LEF; this instead shrinks the kernel to elementary abelian while keeping a large linear quotient.
  mf-is-commensurability-invariant: That is the positive permanence statement for finite index; this is the negative statement for split extensions, and the pair delimits which extensions preserve MF.
artifacts:
  - GroupApproximation/Sofic/AscendingHNNSplitExtension.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

Take `K = C2` in the compression wreath family, `A = C2^(G*/Gamma*)`, so that

    1 -> A -> W_{C2} -> G* -> 1

is **split**, with

- `A` elementary abelian of exponent two, locally finite, amenable,
  residually finite, MF, MAP, and linear over `F_2(t_1, t_2, ...)`;
- `G*` finitely generated, residually finite, linear over `Q`, MF, and MAP;
- `W_{C2}` finitely generated, sofic, hyperlinear, and **not** MF, not
  residually finite, not MAP, and not linear over any field.

So MF survives neither a split extension with an abelian kernel nor one with a
linear quotient; the same sequence witnesses the failure of residual
finiteness and of maximal almost periodicity, and the failure of "linear over
some field" (the two factors are linear over fields of different
characteristic).

The abelian kernel is the point.  With a nonabelian locally finite kernel one
might blame the kernel; here the kernel is as tame as an infinite group gets,
and the obstruction is entirely in how the quotient acts on it.
