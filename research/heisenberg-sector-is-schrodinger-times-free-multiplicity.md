---
rg: 2
id: heisenberg-sector-is-schrodinger-times-free-multiplicity
kind: claim
title: A nontrivial finite Heisenberg sector is one Schrödinger block times a free multiplicity gauge
distinct_from:
  hs-finite-heisenberg-windows-have-compatible-density-measures: that gives branching densities for arbitrary finite possibly degenerate root windows; this gives the complete representation and transporter normal form on one nondegenerate Heisenberg central phase.
  finite-tags-do-not-atomize-heisenberg-schrodinger-tower: that computes atom decay and a growing commutant along the standard tower; this classifies every representation and every fixed-center automorphism implementer at one level.
  coherent-heisenberg-multiplicity-decoder: that must use full affine-Leavitt return relations to construct four compatible coefficient operators; this proves that finite Heisenberg representation theory leaves their multiplicity gauges completely free.
---

**ESTABLISHED EXACT NORMAL FORM.**  Fix a prime `p` and let

```text
H_N=<X(v),Y(w),Z : [X(v),Y(w)]=Z^(<v,w>)>,
                 v,w in F_p^N,                         (HSF1)
```

with the standard nondegenerate pairing and the usual additive and central
relations.  Let `rho:H_N->U(K)` be finite-dimensional, let `zeta!=1` be a
`p`th root of unity, and let

```text
K_zeta=1_{ {zeta} }(rho(Z))K.                         (HSF2)
```

There is an integer `m_zeta>=0` and a unitary identification

```text
K_zeta ~= l2(F_p^N) tensor C^(m_zeta),
rho|_(K_zeta) ~= pi_(N,zeta) tensor I_(m_zeta),        (HSF3)
```

where `pi_(N,zeta)` is the unique irreducible representation with central
character `Z mapsto zeta` and has dimension `p^N`.  In particular

```text
dim K_zeta=p^N m_zeta,
rho(H_N)'|_(K_zeta)=I_(p^N) tensor M_(m_zeta)(C).      (HSF4)
```

For the maximal abelian subgroup `X(F_p^N)`, each of its `p^N` character
projections on `K_zeta` has rank exactly `m_zeta`.  Hence every one has
central-sector-normalized trace `p^(-N)` when `K_zeta` is nonzero,
independently of the multiplicity.

There is an equally sharp transporter statement.  Let `alpha` be any
automorphism of `H_N` fixing `Z`, and suppose `W` implements `alpha` on
`K_zeta`:

```text
W rho(h) W^*=rho(alpha(h))             (h in H_N).     (HSF5)
```

Choose one Schrödinger implementer `U_alpha` of `alpha`.  Then, under
`(HSF3)`, every such `W` has the form

```text
W=U_alpha tensor V,                    V in U(m_zeta), (HSF6)
```

and every `V in U(m_zeta)` is allowed.  Thus the full finite Heisenberg
multiplication table, the nontrivial central phase, all polarized character
multiplicities, and the implemented automorphism determine the label
operator but impose **no condition at all** on its multiplicity unitary.

For the coordinate inclusion `H_N<=H_M`, the Schrödinger restriction is

```text
pi_(M,zeta)|_(H_N)=p^(M-N) pi_(N,zeta).                (HSF7)
```

Consequently the compatible scalar branching densities synchronize exactly
the integer factor in `(HSF7)` and the central-phase mass, but they do not
select an inter-level identification: its exact gauge contains
`U(p^(M-N))`.  If `M>N`, a cyclic shift in this gauge has normalized
Hilbert--Schmidt distance `sqrt(2)` from the identity while preserving every
datum just listed.  Tensoring any fixed finite tag leaves the same subgroup
of gauges by placing the identity on the tag factor.

For `coherent-heisenberg-multiplicity-decoder`, this exhausts what finite
Heisenberg representation theory alone can contribute.  There is no hidden
irreducible-type mismatch left to repair on a nontrivial central phase; the
remaining problem is precisely to constrain several operators in the free
matrix factor of `(HSF4)` by a same-reservoir affine-Leavitt return.

DERIVATION
nontrivial-heisenberg-sector-normal-form-proof
