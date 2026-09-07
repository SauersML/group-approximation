---
rg: 2
id: leavitt-nested-idempotent-corner-module-equivalence
kind: claim
title: The trace-balanced nested corner absorbs its own proper sub-corner
distinct_from:
  leavitt-trace-balanced-nested-idempotents: that constructs the pair and proves every degree-zero obstruction vanishes on it; this is the module isomorphism itself, which that construction deliberately does not assert.
  leavitt-e-f-murray-von-neumann-equivalence: that is the refuted equivalence for the earlier corner pair, killed because the two identity coefficients differ; this is the same question for a different pair, built so that the whole cocenter agrees and that refutation cannot run.
  leavitt-corner-one-sided-lift-exists: that corrects an arbitrary lift of a Leavitt relation inside the unital corner eAe; this asks for an isomorphism of two canonical projective modules and names both idempotents explicitly.
artifacts:
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
---

With `S=F_2[Q]` and `e, f` the idempotents of
`leavitt-trace-balanced-nested-idempotents`, so that `0 != f < e`:

```text
e S ~= f S       as right S-modules.                    (NIE1)
```

Equivalently there are `x in eSf` and `y in fSe` with

```text
x y = e,                    y x = f.                    (NIE2)
```

This is a **Hilbert hotel for one explicit projective module**: `eS` would
contain the proper direct summand `fS` and be isomorphic to it.

## Attempts

Nothing has been tried yet beyond the obstruction audit that produced the
pair.  What that audit establishes is which arguments can no longer be run
against `(NIE1)`, and the honest reading is that the pair was designed to
evade the known refutations, not that it was shown to satisfy them.

* *The coefficient-trace refutation.*  This is what killed the previous pair:
  `group-algebra-coefficient-trace-separates-leavitt-corners` computes
  different identity coefficients for the two idempotents, and cyclicity of
  the trace forbids `xy=e`, `yx=f`.  It does not run here.  Both `e` and `f`
  have augmentation zero and zero image in the cocenter `S/[S,S]`, so **every**
  conjugacy-class coefficient trace agrees on them — a single involution
  conjugates `g` to `g^(-1)` and `h` to `h^(-1)` simultaneously, and the terms
  pair off in characteristic two.
* *The quotient obstruction.*  `pi(e)=1` and `pi(f)=p` are already
  Murray--von Neumann equivalent in `R`, so evaluation raises no objection
  either.  This is necessary and nowhere near sufficient:
  `direct-finiteness-not-inherited-by-quotients` is exactly the warning that
  an equivalence downstairs proves nothing upstairs, and the whole content of
  `(NIE1)` is the part that does not descend.
* *The support obstruction.*  `subgroup-supported-one-sided-inverse-rigidity`
  would kill the pair if `x` and `y` could be confined to a subgroup with
  directly finite group algebra.  They cannot be confined a priori — `x` and
  `y` are unconstrained elements of `S` — so the lemma gives no information
  here, which is neither good news nor bad.

**Where the attack should start.**  `eS` and `fS` are modules over
`F_2[C_3 x C_3]`-corners induced up to `S`, so Mackey restriction to the
finite subgroup `<g,h>` and its idempotent decomposition is the first tool;
after that, cross-atlas Hecke bimodules for the double cosets of `<g,h>` in
`Q`.  Word enumeration is the wrong instrument and should not be reached for.

**What would refute it.**  Any additive invariant of finitely generated
projective `S`-modules that separates `[eS]` from `[fS]` — a rank function, a
`K_0` class, a trace surviving the cocenter collapse.  A refutation is as
valuable as a proof here, because it would say what the trace-balancing bought
and what it did not, and the pair is canonical enough that the answer would
transfer to every construction of this shape.
