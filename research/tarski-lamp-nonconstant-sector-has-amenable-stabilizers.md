---
rg: 2
id: tarski-lamp-nonconstant-sector-has-amenable-stabilizers
kind: claim
title: The nonconstant lamp sector of a Tarski actor is invariant, amenably stabilized and half the trace
artifacts:
  - research/artifacts/atomic-schreier-lamp-collapse-audit-2026-08-26.md
distinct_from:
  infinite-schreier-pvm-transport-kills-finite-mark: that is the general mass collapse for any orbit graph with a bottom spectral gap; this is the concrete instance -- one actor, one two-lamp marked word, and the verification that the invariance, stabilizer and mass hypotheses actually hold there.
  hyperlinear-wreath-model: that is the Kun--Thom coset wreath over a Kazhdan pair, where the point stabilizers are conjugates of the Kazhdan subgroup and the known permanence hypothesis FAILS; this is the regular lamp module over an actor whose proper subgroups are all amenable, where that hypothesis holds and therefore prices the construction rather than helping it.
  coset-wreath-is-hyperlinear: that is the open hyperlinearity question for the arithmetic summit wreath W_3; this states elementary spectral facts about a Tarski lamplighter and asserts nothing about its hyperlinearity.
---

Let `A` be a finitely generated group with a finite symmetric generating set
`S` such that `A` is nonamenable and **every proper subgroup of `A` is
amenable**; Ol'shanskii's Tarski monsters, in which every proper nontrivial
subgroup has order `p`, are the model example and are `2`-generated.  Let

```text
M = direct sum over A of C_2,   Gamma = M rtimes A = C_2 wr A,
M^ = {+1,-1}^A,   (s.chi)(x) = chi(s^(-1) x),
```

fix `a =/= e` in `A`, and let `w = m_e m_a in M`, so `chi(w) = chi(e) chi(a)`.
Write `(R_a chi)(x) = chi(x a)` for the right translation and put

```text
Omega = { chi in M^ : R_a chi =/= chi }.                            (TLS1)
```

Then

```text
(1) Omega is A-invariant;
(2) { chi : chi(w) = -1 } is contained in Omega;
(3) Stab_A(chi) is a PROPER, hence amenable, subgroup for every chi in Omega;
(4) tau(w) = 0 and w^2 = 1 in the canonical trace of Gamma, so the negative
    spectral sector of w carries mass exactly 1/2;
(5) in any tracial (N,tau) and any self-adjoint unitary U_w in N, the mass of
    the (-1)-sector of U_w is || U_w - 1 ||_2^2 / 4.
```

Clause `(1)` is the correction the mechanism needs: the negative sector
`{chi(w) = -1}` of the marked word is itself **not** invariant, so it is not a
union of orbits and cannot be fed to a Schreier-graph estimate directly; its
saturation `(TLS1)` is invariant, keeps the whole mass by `(2)`, and still
excludes precisely the constants, which is what `(3)` needs.  With `(3)` and
`kesten-amenable-stabilizer-uniform-gap` the orbit graph of `Omega` has bottom
gap `gamma = 1 - rho(A,S)`, which is the hypothesis `(ISP1)` of
`infinite-schreier-pvm-transport-kills-finite-mark`.

Clause `(5)` is the marking convention in a form with no constants in it: an
`alpha`-separated marked involution in a microstate carries `alpha/4` of the
trace in its negative sector, which is what a decoded resolution must reproduce.
