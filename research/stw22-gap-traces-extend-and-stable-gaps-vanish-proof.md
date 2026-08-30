---
rg: 2
id: stw22-gap-traces-extend-and-stable-gaps-vanish-proof
kind: route
title: Extend ideal traces to norm fibres and annihilate stable gaps
target: stw22-tracefree-fibre-gap-ideals-force-trace-continuity
requires:
  - stw01-stable-algebras-are-bounded-quasitrace-invisible
  - stw22-norm-fibre-gap-is-the-trace-obstruction
artifacts:
  - research/artifacts/stw22-tracial-completion-fibre-gap-audit-2026-08-30.md
---

Fix `x` and abbreviate `B=B_x` and `I=I_x`.  If `phi` is a tracial state on
`B`, then `phi|I` is a bounded positive trace.  Thus `(TF_x)` makes every
tracial state on `B` annihilate `I`.

Conversely, let `sigma` be a nonzero bounded positive trace on `I`.  The
standard norm-preserving extension of a positive functional on an ideal,
computed along any contractive approximate identity `(e_lambda)` of `I`, is

```text
tilde sigma(b)=lim_lambda sigma(b^(1/2)e_lambda b^(1/2)),
                                                        b in B_+,
```

followed by linear extension.  Equivalently, extend `sigma` strictly to
`M(I)` and compose with the canonical multiplication homomorphism
`B -> M(I)`.  The extension remains tracial: on products this follows first
when one factor lies in `I` from the trace identity in `I`, and then in
general by inserting `(e_lambda)` on both sides and passing to the limit.
Moreover `tilde sigma|I=sigma` and
`||tilde sigma||=||sigma||`.  Since `B` is unital, normalization gives a
tracial state on `B` which does not annihilate `I`.  Hence

```text
every trace on B kills I
  iff I has no nonzero bounded positive trace.             (*)
```

Applying `(*)` at every `x` and then
`stw22-norm-fibre-gap-is-the-trace-obstruction` proves the first conclusion.

If `I` is stable, the prerequisite says that every bounded `2`-quasitrace on
`I` vanishes.  A bounded positive trace is a bounded `2`-quasitrace, so
`(TF_x)` follows.  No sigma-unitality assumption is needed.

Finally take `B=K(ell^2)^~` and `I=K(ell^2)`.  The ideal is nonzero and
stable, while `B/I=C`.  The conclusion already proved shows that every trace
on `B` annihilates `I`; the quotient character supplies the unique trace.
For the one-point central bundle, `J=0` and the trace kernel of that character
is exactly `K(ell^2)`, proving that the stable-gap hypothesis does not imply
`J=K`.
