---
rg: 2
id: fixed-finite-label-km-holonomy-is-scalar-or-gapped
kind: claim
title: Fixed finite-label Kac-Moody holonomy is projectively scalar or has a uniform relator gap
distinct_from:
  finite-projective-sector-groupoids-have-conjugate-absorbers: that classifies finite projective label arrows and leaves an arbitrary contextual multiplicity representation; this uses simplicity of the Kac--Moody lattice to rule out every nontrivial globally flat finite label system and gives the exact nonscalar-face gap.
  finite-face-flatness-stops-at-fundamental-group-holonomy: that classifies bare unitary connections by fundamental-group representations; this treats label intertwiners tensored with arbitrary multiplicity holonomy and shows the finite label cannot strengthen the face equations.
  compact-hyperbolic-km-regular-microstates-synchronize: that permits arbitrary growing and entangled regular-core overlap maps; this rules out only fixed finite projective-label/Schur-product schemes.
---

**ESTABLISHED.**  Fix the infinite finitely generated simple Kac--Moody
lattice `Gamma=<S|R>` from `simple-kazhdan-kac-moody-lattices-exist`.  Let
`W` be a fixed finite-dimensional label space and assign a unitary `C_s` to
each generator.  This includes a finite projective sector-groupoid bisection
after putting its object spaces in one direct sum.  At multiplicity `k`, let

```text
U_s=C_s tensor Q_s,          Q_s in U(k).               (FLK1)
```

For each relator `r`, write `C_r` and `Q_r` for the corresponding words.
Exactly one of the following occurs.

1. Some `C_r` is nonscalar.  Then every multiplicity choice satisfies

```text
||r(U)-I||_2^2
 =2-2 Re(tau_W(C_r) tau_k(Q_r))
 >=2-2|tau_W(C_r)| >0.                                 (FLK2)
```

Thus the fixed label scheme has a dimension-independent relator gap.
2. Every `C_r` is scalar.  Then `s -> [C_s]` defines a projective unitary
   representation `Gamma->PU(W)`, and it is trivial.  Hence every `C_s` is
   scalar and the label system has no nontrivial sector permutation,
   adjoint action, or finite-subgroup regular block.

Consequently no fixed finite-label twisted-holonomy scheme of the Schur form
`(FLK1)` can be the missing regular-core synchronization mechanism.  It
either already pays a fixed presentation-relator defect or becomes invisible
and leaves the entire multiplicity problem unchanged.  The first surviving
native coupling must leave this class, for example through a coherent
additive same-block sum of several label paths, an overlap map which entangles
label and multiplicity coordinates rather than normalizing the finite label
algebra, or label complexity growing with the microstate multiplicity.
