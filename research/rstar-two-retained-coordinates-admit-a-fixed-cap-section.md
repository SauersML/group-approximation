---
rg: 2
id: rstar-two-retained-coordinates-admit-a-fixed-cap-section
kind: claim
title: Any two retained R-star coordinates admit a section through one fixed maximal Fano cap
distinct_from:
  rstar-private-tail-fiberwise-cap-collapse: that retains one prescribed coordinate and assumes the other three variables are occurrence-private; this finite section lemma retains any set of at most two coordinates.
  rstar-cap-support-is-one-character-row: that characterizes cap support after it is present; this constructs a cap-valued section of every zero-, one-, or two-coordinate projection of R-star.
---

**ESTABLISHED.**  Let `K` be any subset of at most two coordinate positions
of

```text
R_*={x in F_2^4 : x_1+x_2+x_3+x_4=1} minus {1000}.       (RTC1)
```

There is a tail position `j in {2,3,4} minus K` such that the maximal cap

```text
C_(e_j)={x in R_* : x_j=1}                               (RTC2)
```

projects surjectively onto `F_2^K`.  Consequently every subset of active
joint values on the retained coordinates has a deterministic section into
one fixed maximal Fano cap.

In operator form, consider a perfect local representation of one `R_*` row
and retain the commuting observables in the positions `K`.  The remaining
observables can be replaced by functions of their joint spectral
projections so that the complete `R_*` predicate is still satisfied and

```text
X_j=-I.                                                   (RTC3)
```

Thus a row with at least two generators that are free to redefine can be
made cap-supported without changing either of the other two generators.
The construction stays inside the original finite von Neumann algebra and
therefore preserves Connes embeddability.

