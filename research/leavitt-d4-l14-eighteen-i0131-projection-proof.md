---
rg: 2
id: leavitt-d4-l14-eighteen-i0131-projection-proof
kind: route
title: Replay and retract all inverse 131 copy projections
target: leavitt-d4-l14-eighteen-i0131-projection-core
requires:
  - leavitt-d4-l14-eighteen-winner-profile-has-two-classes
---

Let `a,b,c,d,e,f,g,h` denote `g4,...,g11`.  Feeding all ten nonempty copy
projections of the three raw carriers into the audited coordinate Tietze
reducer returns no residual relator and the images

```text
g0=1,                 g1=d^-1 b^-1,
g2=c^-1 a^-1,         g3=1,
g4=a, g5=b, g6=c, g7=d, g8=e, g9=f, g10=g, g11=h,
g12=b^-1 a c,         g13=b d.
```

The compression script reconstructs those ten projections from the raw
class compiler, reruns `close_tietze`, and asserts exact equality with this
empty-residual state.  It then substitutes the displayed true free-group
words into the full, nonabelian carrier and boundary words.  The first
carrier vanishes; the remaining carriers have copy-color words

```text
R2: 3,2,3,2,3
R4: 3,2,1,2,1,0,1,0,1,0,1,2,1,2,3,
    2,1,2,1,0,1,0,1,0,1,2,1,2,3
```

and lengths `5` and `29`.  Every copy projection of both is asserted empty.
The raw boundary reduces from 81 to 51 syllables.  MSI job `16685370` applies
the all-maximal noncrossing forest and coordinate-state semiring to the two
remaining carriers.  This claim records only the exact, exhaustive
projection retraction; it does not infer a boundary survivor.
