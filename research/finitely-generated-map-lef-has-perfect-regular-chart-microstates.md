---
rg: 2
id: finitely-generated-map-lef-has-perfect-regular-chart-microstates
kind: claim
title: A finitely generated minimally almost periodic LEF group has perfectly synchronized regular finite-chart microstates with no global correction
distinct_from:
  finite-subgroup-near-regular-has-large-regular-core: that extracts a regular core from one approximate finite-subgroup table; this gives one microstate sequence on which every fixed finite subgroup is eventually exactly regular and all such charts already live in a common finite regular representation.
  compact-hyperbolic-km-regular-microstates-synchronize: that has a fixed finite presentation and asks its native Kac--Moody relators to rule out the phenomenon; this proves that finite generation, minimal almost periodicity, canonical trace and perfect local chart coherence do not do so.
  exact-codensity-does-not-imply-matricial-rcc: that uses the infinitely generated finitary alternating direct factor to refute relative-commutant collapse; this uses a finitely generated simple LEF group and concerns simultaneous regular finite-subgroup charts and global representation correction.
---

**ESTABLISHED.**  Let `T` be a minimal Cantor subshift for which the derived
topological full group

```text
H=[[T]]'
```

is one of the Fournier-Facio--Gerasimova--Spaas examples recorded in
`ffgs-local-hs-examples-resist-split-finite-presentation-wrappers`.  Thus
`H` is finitely generated, infinite, simple, amenable and LEF.  There are
finite groups `Q_n` and maps

```text
theta_n:H->Q_n,                 phi_n=lambda_(Q_n) o theta_n             (FRL1)
```

with the following simultaneous properties.

1. On every fixed finite subset of `H`, `theta_n` is eventually injective
   and exactly multiplicative.  Hence `phi_n` is a canonical regular-trace
   normalized-Hilbert--Schmidt microstate sequence.
2. For every fixed finite subgroup `K<=H`, eventually

   ```text
   phi_n|K is isomorphic to [Q_n:theta_n(K)] lambda_K.                    (FRL2)
   ```

   There is no residual summand: the regular-core density is exactly one.
3. Any finite family of finite subgroups and overlap inclusions is eventually
   realized inside the **same** regular representation `lambda_(Q_n)`.
   Thus all local charts, their matrix units and their overlap maps are
   already globally synchronized on that finite window; there is no
   multiplicity-commutant cycle to choose.
4. Nevertheless the sequence is not flexibly close to genuine
   finite-dimensional representations of `H`.  Every such representation is
   trivial, while for every fixed `1!=g in H`,

   ```text
   ||phi_n(g)-I||_2=sqrt(2)                                               (FRL3)
   ```

   eventually.  The same lower bound holds after comparison through an
   isometry and an `o(dim)` flexible dimension change.

Consequently no dimension-free synchronization theorem can start only from
finite generation, minimal almost periodicity, canonical regular trace,
finite-subgroup regular cores, and coherence of every fixed finite chart.
Those hypotheses hold here in their exact strongest forms, yet the growing
finite window escapes to infinity.  For the compact-hyperbolic Kac--Moody
candidate, a proof must consume its **fixed finite presentation** (and in
particular a native relation coupling the growing multiplicity coordinates),
not merely improve the local regular-core or overlap-selection theorem.

