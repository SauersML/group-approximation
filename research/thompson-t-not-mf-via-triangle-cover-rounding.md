---
rg: 2
id: thompson-t-not-mf-via-triangle-cover-rounding
kind: route
title: T is not MF from a relator gap on honest Delta(4,3,5)-representations plus doubled, trivially padded rounding of T-near pairs onto them
target: thompson-t-has-full-mf-radical
requires:
  - thompson-t-not-mf-iff-triangle-gap-and-rounding
  - thompson-t-triangle-genuine-rep-relator-gap
  - thompson-t-near-pairs-round-to-triangle-reps
---

**Assembly.**
- Item 1 of `thompson-t-not-mf-iff-triangle-gap-and-rounding` says that `T` is not MF if and only if
  (R_Delta) and (S_T) both hold.
- (R_Delta) is `thompson-t-triangle-genuine-rep-relator-gap`.
- (S_T) is `thompson-t-near-pairs-round-to-triangle-reps`.
- `T` is simple, so "not MF" is "full MF radical".

**Holes.** Both prerequisites are OPEN. By item 2 of the equivalence, each is also *necessary*, so this
route loses nothing. A refutation of either one refutes the target. (S_T) may be replaced by the T-free
(S_Delta).

**What cannot supply (S_T).** Padded stability with a nontrivial auxiliary block, in the sense of
Willett's `R` or `R_q` stability, cannot supply it (`thompson-t-padded-cover-stability-is-inert`). The
conjugate summand cannot be dropped unless (PW) is proved first (item 4 of the equivalence).
