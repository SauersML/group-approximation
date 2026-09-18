---
rg: 2
id: fp-simple-envelopes-not-computable-from-presentations-proof
kind: route
title: A uniform envelope on the BORS halting family, or on its acceptors, would decide halting by uniform Kuznetsov search
target: fp-simple-envelopes-not-computable-from-presentations
requires: [uniform-hosts-force-uniform-word-problem, polynomial-dehn-fp-groups-have-nonuniform-word-problem]
---

Let `P_e`, `H_e`, `x_e`, `y_e` be as in
`polynomial-dehn-fp-groups-have-nonuniform-word-problem`, and let `M_e` and
`G_e` be as in its proof, Step 1.

**Part 1.**  Suppose the partial algorithm exists.  Each `P_e` has Dehn
function `≼ n^18` by item (1), so the algorithm halts on `P_e` with a
Boone--Higman output.  Apply clause (S) of `uniform-hosts-force-uniform-word-problem`
with `w_e := [x_e, y_e]` and `v_e := x_e`.  Here `v_e != 1` by item (3).  So
`{e : [x_e, y_e] = 1 in H_e}` is decidable.  By item (4) this is the halting
set, a contradiction.

**Part 2.**  Suppose the partial algorithm exists.  Each `M_e` accepts the word
problem of the two-generated group `G_e` with time function `<= C_e n^2`.  The
algorithm therefore halts on `M_e` with a presentation `Q_e` of a simple group
`S_e` and words `phi_e(a)`, `phi_e(b)` defining an embedding `G_e -> S_e`.

- *Halting is r.e.:* run `phi_e(0)`.
- *Divergence is r.e.:* compute `Q_e`, `phi_e(a)`, `phi_e(b)`, and enumerate the
  consequences of the relators of `Q_e` together with `[phi_e(a), phi_e(b)]`.
  Halt when `phi_e(a)` appears.
  - If `phi_e(0)` diverges, `[a,b] != 1` in `G_e = F_2`.  So its image
    normally generates the simple group `S_e`, and `phi_e(a)` is found.
  - If it halts, the added relator is already trivial in `S_e`, and `phi_e(a)`
    is never found, because `a` has infinite order in `G_e = Z^2`.

So halting is decidable, a contradiction.  This is clause (S) run over the
computable sequence of acceptors instead of presentations.  The proof of (S)
uses the presentation of `Gamma_e` only to enumerate `w_e = 1`, and here the
acceptor does that job.

**Variant.**  If `S` is only required to have solvable word problem and the
output includes a decision procedure `A_e` for it, run `A_e` on
`[phi_e(a), phi_e(b)]`.  The same contradiction follows, with no simplicity
used.
