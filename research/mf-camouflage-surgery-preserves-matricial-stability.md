---
rg: 2
id: mf-camouflage-surgery-preserves-matricial-stability
kind: claim
title: MF camouflage surgery preserves matricial stability exactly
root: true
artifacts:
  - research/mf-camouflage-surgery-preserves-matricial-stability-proof.md
requires:
  - mf-camouflage-surgery
  - split-mf-equivalences-preserve-matricial-stability
distinct_from:
  mf-camouflage-surgery: that identifies all outgoing MF and norm-corona representations and computes the hidden kernel; this derives the new approximation-repair property of the resulting group.
  matricially-stable-groups-exist: that proves stability of free groups and the integers; this converts every such visible group into a stable non-MF group with a prescribed one-word radical.
  full-mf-radical-uniform-asymptotic-collapse: that obtains degenerate stability when every asymptotic representation is trivial; this permits an arbitrary stable visible quotient and generally has many nontrivial asymptotic representations.
---

For the camouflage group

```text
C_d(Q)=B*_(<d>)(Q x <d>)                              (CMS1)
```

and its split quotient `pi_Q:C_d(Q)->Q`, one has

```text
C_d(Q) is point-norm matricially stable
 iff Q is point-norm matricially stable.               (CMS2)
```

Indeed `mf-camouflage-surgery` gives `(SCE2)` for every norm matrix corona,
and the quotient has its canonical section.  Apply
`split-mf-equivalences-preserve-matricial-stability`.

If `Q` is both MF and matricially stable, then

```text
Rad_MF(C_d(Q))
 =Rad_fd(C_d(Q))
 =ker(pi_Q)
 =normalClosure(d),                                    (CMS3)
```

while `d!=1`.  Thus `C_d(Q)` is a matricially stable non-MF group whose
entire failure of finite-dimensional separation is the one-word hidden
kernel, and whose complete visible MF representation theory is that of `Q`.

Taking `Q=F_r` or `Q=Z` gives concrete stable non-MF groups.  With the
finitely presented Hilbert-hotel seed, these groups are finitely presented
for finite `r`.  More broadly, every finitely presented group which is both
MF and point-norm matricially stable occurs as the universal MF quotient of
a finitely presented stable non-MF group with singly normally generated MF
radical.
