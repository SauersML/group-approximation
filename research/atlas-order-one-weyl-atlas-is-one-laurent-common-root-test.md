---
rg: 2
id: atlas-order-one-weyl-atlas-is-one-laurent-common-root-test
kind: claim
title: Order-one Weyl models on the three-label Atlas slice are exactly one Laurent common-root test
distinct_from:
  atlas-three-label-mode-small-phase-weyl-hits-commutative-wall: that treats the standard phases tending to one and proves a commutative limit; this treats arbitrary rational Weyl phases converging to a fixed nonidentity point of the circle and retains full positive-density commutator spectrum.
  atlas-three-label-mode-two-unitary-moment-reduction: that writes the packet in arbitrary two-unitary moments; this evaluates all those moments in the canonical rotation trace and reduces feasibility to finitely many one-variable Laurent equations.
  atlas-commutative-q14-bands-promote-or-pay: that takes a Laurent gcd for one binary q14 chart parameter and proves rank promotion; this is a complex normalized-HS positive construction criterion using noncommuting Weyl pairs and the regular-A8 packet.
---

**ESTABLISHED POSITIVE REDUCTION.**  Fix `z in T`, `z!=1`.  Choose coprime
integers `p_n,q_n`, with `q_n->infinity`, such that

```text
z_n=exp(2 pi i p_n/q_n) -> z.                         (OWA1)
```

Let `S_n,D_n in U(q_n)` be the irreducible Weyl pair

```text
S_n D_n=z_n D_n S_n,       C*(S_n,D_n)=M_(q_n)(C),    (OWA2)
```

and insert `Z_1=S_n`, `Z_2=D_n` in the exact three-label unitary `(TLM3)`.
For a coefficient word `m`, write

```text
m(S_n,D_n)=z_n^(Area(m)) S_n^(a(m)) D_n^(b(m)).       (OWA3)
```

For each fixed literal Atlas word `s`, define the Laurent polynomial

```text
f_s(t)=sum_({i,j : a(M_s(i,j))=b(M_s(i,j))=0})
          c_s(i,j) t^(Area(M_s(i,j))).                (OWA4)
```

Then

```text
lim_n ||pi_(U_n)(s)-I||_2^2=2-2 Re f_s(z).            (OWA5)
```

Consequently the following are equivalent.

1. The order-one Weyl sequence `(OWA1)` kills every member of `bar_S`.
2. `f_s(z)=1` for every `s in bar_S`.
3. In the canonical trace of the rotation algebra

   ```text
   A_z=C*(u,v | uv=zvu),
   ```

   the three-label relative unitary satisfies every packet word exactly in
   the tracial GNS representation.

If these conditions hold for one non-torsion `z`, then the binary Leavitt
unit group is hyperlinear, hence is an explicit hyperlinear nonsofic group.
Indeed the rational pairs `(OWA2)` are already the required matrix
microstates in the canonical regular-A8 criterion.

This family passes every currently established **coefficient-shape** fence.
Its coefficient algebra is the full growing matrix algebra; and

```text
|S_n D_n-D_n S_n|=|z_n-1| I,                          (OWA6)
```

so the commutator has full support and a singular-value floor tending to
`|z-1|>0`.  Thus neither bounded internal size, block monomiality, vanishing
commutator norm, nor concentration on an `o(q_n)` corner excludes it.  The
literal Laurent equations `(OWA4)` are the first unresolved test.

No root of unity can satisfy all equations `(OWA4)`, but the reason passes
through the **rational rotation algebra**, not one fixed Weyl trace.  If `z`
has finite order, its rotation algebra is a subhomogeneous continuous
`M_q`-bundle and its canonical trace is faithful.  Conditions `(OWA4)` make
every packet unitary have trace one, hence equal the identity in the faithful
tracial GNS representation and therefore in the algebra itself.  Evaluation
in any finite-dimensional fiber then gives a nontrivial exact frozen-A8
atlas, contradicting finite-dimensional invisibility.  One cannot replace
this argument by directly evaluating `(OWA4)` in a fixed irreducible Weyl
pair: additional monomials with exponent sums divisible by `q` survive in
that fiber, since the canonical rational-rotation trace integrates over the
center.  In particular `z=1` is also excluded.

The claim does not assert that a common root exists.  It turns this structured
positive-density construction into a finite symbolic decision problem and
isolates the exact remaining equations.

DERIVATION
atlas-order-one-weyl-common-root-proof
