---
rg: 2
id: one-round-v4-lamps-wordize-a-bcs-losing-projection
kind: claim
title: One V4 lamp per answer wordizes a single BCS losing projection
distinct_from:
  controlled-linear-predication-normal-form: that gives the abstract corner-gating identities for arbitrary involutions; this identifies the gates as coordinate lamps in a finite elementary-abelian group and computes the single losing word explicitly.
  product-word-stabilizers-cannot-linearize-one-losing-corner: that rules out a functorial Alice-times-Bob stabilizer of every allowed vector; this is a selected-representation construction using non-product controlled lamps and makes no soundness claim for other representations.
  finite-morita-toricization-cannot-encode-nonaffine-support: that rules out a representation-functorial finite-Morita compiler for nonlinear answer support; this only wordizes one losing projection after its PVM and Bob involution have already been selected.
---

Let `Omega` be a nonempty finite answer set, let `(P_a)_(a in Omega)` be a
PVM on a Hilbert space `H`, and let `B` be a self-adjoint involution commuting
with every `P_a`.  Fix a forbidden set `F subseteq Omega` and a sign function

```text
s : Omega \ F -> {+1,-1}.
```

The associated one-round losing projection is

```text
L_(F,s,B)
 = sum_(a in F) P_a
   + sum_(a notin F) P_a (1-s(a)B)/2.                 (VL1)
```

Put

```text
V_Omega = product_(a in Omega) <z_a,b_a |
          z_a^2=b_a^2=[z_a,b_a]=1>,                  (VL2)
```

so `V_Omega ~= (C_2 times C_2)^Omega` is finite.  There is a unitary
representation `pi_(P,B)` of `V_Omega` on `H` given by

```text
pi(z_a)=1-2P_a,
pi(b_a)=1-P_a+P_a B.                                 (VL3)
```

Moreover, the ordinary group word

```text
r_(F,s)
 = product_(a in F) z_a
   product_(a notin F) b_a
   product_(a notin F, s(a)=-1) z_a                  (VL4)
```

satisfies

```text
pi_(P,B)(r_(F,s)) = 1-2L_(F,s,B).                    (VL5)
```

Thus one fixed BCS verifier round has an exact finite-lamp wordization once
the answer PVM and the Bob involution have been selected.  In particular,
for a context `c` and queried variable `x`, take `Omega` to be all context
assignments, `F` the forbidden assignments, and `s(a)=a_x` on the allowed
assignments.  Then `(VL1)` is exactly the losing projection `L_(c,x)` in
`two-copy-bcs-game-hamiltonian-dominates-fanizza-signal`.

## Proof

The operator `1-2P_a` is an involution.  Because `P_a` commutes with `B`,

```text
(1-P_a+P_aB)^2=1-P_a+P_aB^2=1.                      (VL6)
```

The two displayed operators commute at the same coordinate.  Operators at
distinct coordinates commute as well: their nonidentity parts are supported
on the orthogonal corners `P_aH` and `P_a'H`.  Hence `(VL3)` respects every
relation in `(VL2)` and defines a representation.  Notice also that

```text
product_(a in Omega) pi(b_a)=B,                       (VL7)
```

because exactly the `a`-th factor restricts to `B` on `P_aH`.

Now restrict `(VL4)` to one summand `P_cH`.  If `c in F`, only `z_c` acts
nontrivially and the result is `-1`.  If `c notin F`, only `b_c` and,
when `s(c)=-1`, `z_c` act nontrivially; the result is `s(c)B`.  Therefore

```text
pi(r_(F,s))
 = -sum_(a in F) P_a + sum_(a notin F) s(a)P_aB
 = 1-2L_(F,s,B),                                     (VL8)
```

which proves `(VL5)`.

## Fourier--wreath interpretation

The first lamp bit is literally a Fourier atom.  In the canonical model
`H=l2(Omega) tensor K`, with `P_a=|a><a| tensor 1` and an involution `B_0`
on `K`, `(VL3)` becomes

```text
z_a -> 1-2|a><a| tensor 1,
b_a -> 1-|a><a| tensor 1 + |a><a| tensor B_0.         (VL9)
```

This representation extends to the finite wreath product

```text
(C_2 times C_2) wr Sym(Omega)
```

by letting `Sym(Omega)` permute the answer basis.  Equivalently it is induced
from the point stabilizer of one answer: at the distinguished coordinate,
`z` acts as `-1` and `b` as `B_0`, while every other lamp coordinate acts
trivially.  Thus the phrase "coordinate lamp equals `1-2P_a`" is exact, not
metaphorical.

## Exact scope of the construction

This is a local completeness theorem, not a groupification soundness theorem.
The relations of `V_Omega` do not force an arbitrary representation to
identify `z_a` with the spectral polynomial `1-2P_a`, nor do they force the
selected answer type.  Finite-group induction supplies the unwanted types,
as recorded in `finite-selector-gadget-induction-barrier` and
`finite-morita-toricization-cannot-encode-nonaffine-support`.

For one fixed Bob question the lamp fiber `C_2 times C_2` is finite.  To use
several generally noncommuting Bob involutions in one common lamp system, the
fiber must contain their Bob group (for example
`C_2 times (*_x C_2)` before further relations), so the full fiber need not
be finite.  Giving each question an unrelated finite `V_4` packet instead
loses the required coherence between repeated occurrences of the same Bob
observable.  That coherence and representation-wide type selection remain
the global return problem; `(VL5)` does not conceal them.
