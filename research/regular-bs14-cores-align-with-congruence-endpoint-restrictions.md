---
rg: 2
id: regular-bs14-cores-align-with-congruence-endpoint-restrictions
kind: claim
title: Every regular exact BS14 core aligns with same-dimensional congruence endpoint restrictions
distinct_from:
  bs14-global-atoms-are-moving-congruence-restrictions: that classifies the restrictions of honest finite-dimensional endpoints; this proves an asymptotic converse on the regular character face without extracting packet multiplicities or a congruence level from the input.
  regular-iwahori-relative-congruence-exactification: that asks to repair the two modular vertices and their common incidence; this authenticates only the amenable BS core and deliberately leaves the adjoining involution unresolved.
  three-way-cell-semigroups-have-conductor-but-unbounded-charge: that exposes lattice charge for a fixed finite cell model; this bypasses cellwise charge on the regular face by approximate unitary uniqueness of embeddings of the whole amenable core.
  fixed-level-bs14-compatible-basin: that cuts long cycles and compares a moving finite-group basin with an explicit error; this is level-free and schedule-free but controls only the core restriction.
---

Put

```text
A=PSL_2(Z[1/2]),
B=<r,t | r t r^(-1)=t^4> <= A.                       (RCA1)
```

Let

```text
beta_n:B -> U(d_n)                                    (RCA2)
```

be exact representations whose normalized characters converge pointwise to
the regular character of `B`:

```text
tr_(d_n)(beta_n(b)) -> delta_(b,e).                   (RCA3)
```

Then there are exact same-dimensional representations

```text
pi_n:A -> U(d_n)                                      (RCA4)
```

and unitaries `W_n in U(d_n)` such that

```text
max_(s in {r,t})
 ||beta_n(s)-W_n pi_n(s) W_n^*||_2 -> 0.              (RCA5)
```

The `pi_n` may be chosen to factor through finite odd congruence quotients,
and their normalized characters converge pointwise to the regular character
of `A`.

This is a same-dimensional, level-free authentication theorem for the exact
BS core.  It neither names the input's fourth-power packets nor rounds their
multiplicity vector in the restriction semigroup.  Instead it uses the fact
that `B` is amenable: canonical-trace embeddings of `L(B)` into a tracial
matrix ultraproduct are approximately unitarily conjugate.

Consequently, on the regular face of the Iwahori problem, every exactified
core may first be replaced at `o(1)` normalized-HS cost by the restriction of
an honest congruence endpoint in the **same dimension**.  Thus neither the
moving affine-semigroup charge nor the one-parameter finite-level basin is
an obstruction to authenticating the core itself.

This authentication does not determine the global endpoint character, even
asymptotically.  `cuspidal-redistribution-refutes-regular-core-orbit-basin`
constructs exact congruence endpoints whose global normalized characters
converge to the regular character, whose BS restrictions equal the regular
congruence restriction exactly, but whose extending involutions remain a
fixed distance from the regular-character endpoint orbit.  Thus `(RCA5)`
cannot be followed by capture to the particular `pi_n` orbit.  The endpoint
representation type must be selected adaptively.

The theorem does not authenticate the supplied adjoining involution `X`.
After conjugating by `W_n`, the input is merely an almost endpoint over an
exact congruence restriction.  Proving that this `X` lies near the exact
core-commutant endpoint orbit remains the relative extension theorem in
`bs14-relative-involution-extension-stability`.  In particular, Selberg
orbit retraction cannot yet be applied to `X`, because `X` has not been
shown to generate an exact congruence modular vertex.
