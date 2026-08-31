---
rg: 2
id: asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope
kind: claim
title: An HNN extension embeds in a central HNN extension of any overgroup where its twist is inner
distinct_from:
  regular-mf-central-hnn-closure: that is the permanence theorem for central HNN extensions; this reduces every asymmetric HNN extension to that theorem by an embedding.
  mf-safe-asymmetric-hnn-replacement: that asks for a finite-presentation gadget replacing the rope edge; this is a structural embedding valid for all HNN extensions and turns the gadget question into an envelope question.
---

ESTABLISHED.  Let `A` be a group, `C_1, C_2 <= A`, `phi : C_1 -> C_2` an
isomorphism, and

```text
A *_phi = < A, t | t c t^-1 = phi(c), c in C_1 >.
```

Suppose `A <= D` and some `u in D` satisfies `u c u^-1 = phi(c)` for all `c
in C_1`.  Then

```text
A *_phi  <=  < D, z | [z, C_1] = 1 >,        t -> u z.                (IE1)
```

Consequently `A *_phi` is operator-MF whenever such a `D` is regularly
operator-MF realized (for example residually finite), and in general

```text
A *_phi is MF   iff   A embeds in an MF group D in which phi is inner.   (IE2)
```

## Proof

Since `A <= D` and the associated subgroups are unchanged, Britton's lemma
shows that the natural map `A *_phi -> D *_phi = < D, t | t c t^-1 = phi(c),
c in C_1 >` is injective: a Britton-reduced word over `A` is Britton-reduced
over `D`.  In `D *_phi` put `z = u^-1 t`.  The relation `t c t^-1 = phi(c) =
u c u^-1` reads `z c z^-1 = c`, so `D *_phi = < D, z | [z, C_1] = 1 >` by a
Tietze transformation.  This is `(IE1)`.

For `(IE2)`, if `A *_phi` is MF take `D = A *_phi` and `u = t`.  Conversely,
if `D` is regularly operator-MF realized, [[regular-mf-central-hnn-closure]]
makes the central HNN extension in `(IE1)` regularly operator-MF realized,
and subgroups of MF groups are MF.  If `D` is only known to embed in the
unitary group of an MF C-star algebra, Shulman's central-HNN theorem (Theorem
25 of arXiv:2603.13564) gives MF of the universal C-star HNN algebra, and
the group-level conclusion needs the trace argument of the regular
realization; the residually finite case is where both are available at once.

## Use

This converts the asymmetric rope edge `(R1)` of
`research/artifacts/fp-mf-pi2-compiler-audit-2026-08-25.md` into the search
for one MF overgroup of `Gamma x Q` in which `(s,1) -> (s,tau(s))` is
implemented by conjugation.  The finite HNN quotients used in
[[twisted-rope-edge-is-mf-under-relative-profinite-compatibility]] are
exactly finite approximations of such an envelope.
