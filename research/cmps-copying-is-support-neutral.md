---
rg: 2
id: cmps-copying-is-support-neutral
kind: claim
title: The CMPS two-oracularization copies clause supports exactly and cannot create Fano caps
distinct_from:
  cmps-lemma20-is-radius-two-incidence-commutation: that records the new commutators obtained by the construction; this records that its chosen completeness representation does not shrink any copied clause support.
  star-surjective-nonaffine-context-blocks-fano-empty-link-lift: that uses all classical satisfying assignments to refute a universal empty-link property after the R-star lift; this is a statement about the actual positive spectral support of the chosen perfect model before that lift.
  fano-cap-witness-sections-force-source-affine-safety: that gives a general necessary condition for a cap-valued R-star witness section; this identifies exactly how the CMPS construction transports the source support to which that condition applies.
---

**ESTABLISHED SUPPORT-NEUTRALITY.**  Let `S` be the value-one `3SAT-5`
instance and perfect representation used at the start of Lemma 20 of
Culf--Mastel--Paddock--Spirig, arXiv:2510.03477v3.  For an original clause
`u` with variables `x,y,z`, write

```text
P_(u,a)=A_x^(a_x) A_y^(a_y) A_z^(a_z),
Supp(u)={a:P_(u,a)!=0}.                                  (CSN1)
```

Lemma 20 replaces the variables in `u` by local copies `x_u,y_u,z_u`, makes
seven labeled copies of that clause, and in its completeness model sets

```text
A_(x_u)=A_x,  A_(y_u)=A_y,  A_(z_u)=A_z.                (CSN2)
```

Consequently, for every one of the seven copied clauses and every local
assignment `a`, its joint spectral atom is literally `P_(u,a)`.  In
particular

```text
Supp(u')=Supp(u)                                         (CSN3)
```

for every copied clause `u'`.  Repetition changes the incidence graph and
creates the radius-two commutators, but it performs no rank reduction,
central compression, or support selection on a copied clause.

It follows that any affine-unsafe source support survives unchanged.  If
an odd subset of `Supp(u)` has xor equal to a forbidden assignment of `u`,
then the same odd subset witnesses

```text
Aff(Supp(u')) not subseteq C_(u').                       (CSN4)
```

For a proper signed 3SAT clause, this includes the important special case
where `Supp(u)` contains a translated Fano line: the xor of the line is the
unique forbidden clause assignment.

Combining `(CSN3)--(CSN4)` with
`fano-cap-witness-sections-force-source-affine-safety` gives a precise
firewall for the subsequent contextwise fixed-language `R_*` reduction.
If one copied clause has affine-unsafe positive support in the chosen CMPS
perfect model, then **no choice of classical pp witnesses** for that model
can make every descended `R_*` occurrence cap-supported.  The sevenfold
copying and the extra two-oracular commutation relations cannot repair the
failure.

This does not prove that the particular hard HALT model has an unsafe
clause.  It moves the remaining positive possibility all the way back to
the original value-one `3SAT-5` representation: one must choose it so that
every original clause support used by the reduction is affine-safe (and
separately check the new equality/implication contexts).  Neither Lemma 20
nor a bounded-rank or irreducible-block choice supplies that property.

