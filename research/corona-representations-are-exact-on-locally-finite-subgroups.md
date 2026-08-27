---
rg: 2
id: corona-representations-are-exact-on-locally-finite-subgroups
kind: claim
title: Corona representations are coordinatewise exact on locally finite subgroups, with exact compressor intertwiners, and this data alone never obstructs
artifacts:
  - research/corona-exact-on-locally-finite-subgroups-proof.md
distinct_from:
  corona-defect-is-not-uniform: that says the coordinate defect of a corona representation of an INFINITE group is not uniform, so Ulam-type stability does not apply; this is the positive complement, exact stability on every finite subgroup with a slowly growing exact radius, plus exact intertwiners for partial conjugations, and it records that the resulting constraint system is regular-satisfiable.
  opnorm-packet-exactification-is-dimension-free: that exactifies approximate matrix-unit packets; this uses it once, through the Wedderburn matrix units of a finite group algebra, to exactify approximate finite-group representations, and then draws the group-level consequences.
  finite-positive-root-fragments-have-marked-regular-models: that builds a regular model of one finite positive-root fragment; this proves that EVERY corona representation is coordinatewise exact on every locally finite subgroup, and that compressor conjugation constraints between finite subgroups are satisfied by regular representations of any common finite overgroup, so the two statements together say no obstruction lives in this data.
  leavitt-one-compressor-defect-lies-in-amenable-subgroups: that exhibits amenable subgroups of the Leavitt group containing the defect; this is a representation-level lemma about arbitrary corona representations and a norm-2 dichotomy on the simple locally finite core.
  degree-zero-leavitt-core-has-locally-finite-marked-models: that gives finite elementary-group models of finite coefficient windows; this is about the structure of arbitrary norm-corona homomorphisms restricted to such windows.
---

**ESTABLISHED.**  Let `Theta:Gamma->U(Q)` be a homomorphism into the unitary
group of a norm matrix corona `Q=prod_k M_(d_k)(C)/directSum_k M_(d_k)(C)`,
and let `Lambda=union_m F_m<=Gamma` be a locally finite subgroup written as
an increasing union of finite subgroups.  Then:

1. **Exact lifts.**  There are unitary lifts `rho_k` of `Theta` and integers
   `m_k->infinity` such that `rho_k|F_(m_k)` is a genuine unitary
   representation of the finite group `F_(m_k)` for every `k`.  The modulus
   depends only on `|F_m|` and the coordinate defect on `F_m`, not on `d_k`.
2. **Exact intertwiners.**  If `gamma in Gamma` and `F<=Lambda` is finite
   with `gamma F gamma^-1<=Lambda`, then for all large `k` there is a
   unitary `T_k` lifting `Theta(gamma)` with

```text
T_k rho_k(g) T_k^* = rho_k(gamma g gamma^-1)        (g in F),          (CEL1)
```

   exactly.  In particular `rho_k|F` and `rho_k|(gamma F gamma^-1)` composed
   with `Ad gamma` are unitarily equivalent representations of `F`.
3. **Exact commutants.**  For finite `F<=Lambda`, the corona commutant
   `Theta(F)'` is the image of the coordinatewise exact commutants
   `{(x_k): x_k in rho_k(F)'}`.
4. **Regular satisfiability.**  Conversely, given any finite group `G`
   containing `F` and a subgroup `F'` with an isomorphism `alpha:F->F'`, the
   left regular representation `lambda_G` admits a unitary `T` with
   `T lambda_G(g) T^* = lambda_G(alpha(g))` for all `g in F`, and every
   constraint of the form 1--3 on a finite tower is satisfied by regular
   representations of finite overgroups.  Hence no MF obstruction is
   contained in locally-finite-subgroup data together with partial
   conjugation data.
5. **Norm-2 dichotomy on the Leavitt core.**  For the binary Leavitt group
   `H=EL_12(R)`, `R=L_(F_2)(1,2)`, and its degree-zero core
   `L_0=EL_3(R_0)=union_m SL_(3*2^m)(F_2)`, every corona homomorphism
   `Theta` of `H` satisfies exactly one of

```text
Theta = 1,        or        ||Theta(g)-1|| >= 2 sin(pi/ord(g))  for all 1!=g in L_0,   (CEL2)
```

   with equality `2` for every involution.  Thus `Rad_MF(H)=H` is
   equivalent to: for every corona homomorphism, the coordinatewise exact
   representations of `SL_(3*2^(m_k))(F_2)` from item 1 are eventually
   trivial.

## What this is for

Items 1--3 are the Property-`(T)`-free replacement for "restrict the
Kazhdan projection": on a locally finite subgroup the fixed-point
projections, isotypic projections, and commutants of every finite subgroup
are genuine corona elements with exact coordinate lifts, and compressors
act on them by exact conjugation.  Item 4 is the firewall: since regular
representations of finite groups restrict to isomorphic subgroups
identically, no chain of such exact identities, however long, can force
triviality; a Property-`(T)`-free collapse must use a quantitative
operator-norm statement at finite coordinates that regular representations
of finite groups violate.  Item 5 says what that statement must deliver
for the Leavitt group: not a small perturbation of the marked root but the
literal triviality of a genuine representation of a huge finite simple
group, so intermediate "the mark is nearly trivial" estimates cannot
exist; the passage is all-or-nothing.

No Property `(T)`, spectral gap, trace, or literature input is used; the
only external step is `opnorm-packet-exactification-is-dimension-free`,
itself proved in the graph.

DERIVATION
corona-exact-on-locally-finite-subgroups-proof
