---
rg: 2
id: finitely-generated-monotracial-nonce-cstar-exists
kind: claim
title: A finitely generated simple monotracial non-CE C-star algebra exists
distinct_from:
  character-rigid-signed-bcs-quotient: that additionally asks for a finite BCS presentation and a generating representation of a character-rigid group; this removes only the abstract monotracial source-algebra issue
  non-ce-twisted-group-factor-exists: that asks for a non-CE canonical twisted group trace; the algebra here is a reduced free product and is not asserted to be a group or twisted-group algebra
---

**ESTABLISHED.** There is a unital finitely generated simple C-star algebra
`D` with a unique tracial state `tau_D`, and `tau_D` is not Connes
embeddable.

Start with the fixed finite BCS algebra carrying a non-Connes-embeddable
trace `tau`.  Pass to its GNS image `A`; the induced trace is faithful, `A`
is still finitely generated, and its GNS von Neumann algebra is unchanged.
Put

```text
A_2=A tensor C(T),       tau_2=tau tensor m_T,
A_1=C*_r(F_2),           tau_1=tau_reg,
D=(A_1,tau_1) * (A_2,tau_2).                         (MNC1)
```

The two canonical free generators `u,v in A_1` satisfy

```text
tau_1(u)=tau_1(v)=tau_1(u* v)=0,
```

and the circle generator `z in A_2` satisfies `tau_2(z)=0`.  Avitzour's
free-product averaging theorem therefore makes `D` simple and its canonical
free-product trace the unique tracial state.

Both factors are finitely generated, so `D` is finitely generated.  The
canonical inclusion `A -> D` is trace preserving.  If `tau_D` were Connes
embeddable, its restriction to `A` would be Connes embeddable, contradicting
the choice of `tau`.  Hence `tau_D` is not Connes embeddable.

This removes monotraciality as an abstract source obstruction in the
character-rigid quotient route.  It does **not** give a finite BCS
presentation of `D`, a group-algebra quotient, or the generating
representation of a character-rigid finitely presented group.  Those are
the remaining groupification inputs.
