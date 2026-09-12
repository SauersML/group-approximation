---
rg: 2
id: stw08-stabilize-unitize-af-embedding-reduction-proof
kind: route
title: Stabilize and unitize while preserving and reflecting AF-embeddability
target: stw08-af-embedding-reduces-to-singular-stable-character-kernels
requires:
  - gabe-traceless-exact-qd-af-embedding
artifacts:
  - research/artifacts/stw08-singular-character-reduction-audit-2026-08-30.md
---

Assertion 1 immediately implies assertion 2.  Conversely, let `A` be a
nonzero separable exact quasidiagonal C-star algebra and put

```text
I=A tensor K,             E=I~,
```

with scalar quotient `chi:E->C`.  Stabilization and unitization preserve
separability, exactness, and quasidiagonality.  The algebra `I` is stable and
is an essential ideal of its unitization.

The key point is that this operation preserves **and reflects** the desired
conclusion.  If `A->F` embeds into an AF algebra, then

```text
A tensor K -> F tensor K
```

is injective and the target is AF.  Unitizing gives an injective map

```text
E=(A tensor K)~ -> (F tensor K)~,
```

whose target is again AF.  Conversely, if `E` embeds into an AF algebra,
then its subalgebra `A tensor e_11` does too.  Therefore

```text
A is AF-embeddable  iff  E is AF-embeddable.                 (SC1)
```

Applying assertion 2 to `E` and then `(SC1)` proves assertion 1.

We now sharpen the form of a counterexample.  A stable C-star algebra has no
nonzero bounded trace.  Indeed, write `I=A tensor K` and choose multiplier
isometries `s_1,...,s_m` with orthogonal ranges.  If `rho` is a bounded trace
on `I` and `a in I_+`, then the elements `s_j a s_j*` are orthogonal and

```text
rho(s_j a s_j*)=rho(a).
```

The equality follows by applying the trace identity to
`a^(1/2)s_j* in I`.  Hence

```text
m rho(a)=rho(sum_j s_j a s_j*) <= ||rho|| ||a||,
```

and letting `m` grow gives `rho(a)=0`.

Every tracial state on `E` consequently vanishes on `I`, factors through
`E/I~=C`, and equals `chi`.  The trace `chi` is quasidiagonal because it is
a one-dimensional representation, and it is nonfaithful because `I!=0`.

Finally suppose that the stable kernel of a counterexample `E` were
traceless in the lower-semicontinuous-weight sense.  It is separable, exact,
and quasidiagonal, so `gabe-traceless-exact-qd-af-embedding` would embed `I`
into an AF algebra.  Unitizing that embedding would embed `E`, contrary to
`(SC1)`.  Thus `I` supports a lower-semicontinuous tracial weight with a
finite nonzero value.  The bounded-trace calculation above forces every
such nonzero weight to be unbounded.  This proves all of the asserted
normal-form properties.

**Trust boundary.**  The only nonformal input is Gabe's traceless theorem.
No UCT, nuclearity, faithful trace, extension permanence of AF-embeddability,
or coherence of unrelated quasidiagonal models is used.
