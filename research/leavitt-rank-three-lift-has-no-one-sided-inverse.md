---
rg: 2
id: leavitt-rank-three-lift-has-no-one-sided-inverse
kind: claim
title: The explicit rank-three Leavitt lifts have no one-sided inverse at any support
distinct_from:
  leavitt-rank-three-lift-inverse-support-thirteen: that bounds the SUPPORT of a completing factor from below, leaving open that one exists at support thirteen or beyond, and it rests on an imported machine enumeration; this says no completing factor exists at any support, and rests on the subgroup the lift is supported in — it supersedes that claim and reproves it vacuously without the enumeration.
  leavitt-rank-three-unit-lift: that constructs the lifts and explicitly does not claim their product is one; this proves that no element of the group algebra can ever be the missing partner for either of them.
  leavitt-corner-one-sided-lift-exists: that asks for SOME pair a,b in the corner with ab = e; this kills one named candidate for a — the compression e t~ e of the explicit lift — and says nothing about pairs built from elements whose support leaves the virtually free subgroup.
  leavitt-unit-group-algebra-not-directly-finite: that is the open Kaplansky failure for the whole group algebra; this is an established no-go for the concrete candidates the corpus had built toward it, and it leaves the conjecture exactly as open as it was.
  binary-leavitt-algebra-not-directly-finite: that is the two-line defect inside the Leavitt algebra itself, which is not a group algebra; this is the statement that the defect refuses to lift along the explicit rank-three material, and it CONSUMES that node as the reason t_0 is not a unit.
artifacts:
  - research/artifacts/leavitt-rank-three-no-inverse-2026-08-18.md
---

With `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, the support-three lifts

```text
t~ = [u_1]+[u_2]+[u_3],     s~ = [v_1]+[v_2]+[v_3]
```

of `leavitt-rank-three-unit-lift`, and the corner idempotent
`e = [g]+[g^2]` of `leavitt-corner-idempotent-unital-surjection`:

1. **`t~` has no right inverse and no left inverse in `A`** — there is no
   `B in A` with `t~ B = 1`, and none with `B t~ = 1`.
2. **The same for `s~`.**
3. **`e t~ e` has no one-sided inverse in the corner `eAe`.**

The mechanism is not size but location: by
`leavitt-rank-three-support-group-is-virtually-free` the whole support of each
lift, and of `e` too, lies in a subgroup isomorphic to `(C_2 x C_2) * C_3`,
whose group algebra is directly finite; by
`subgroup-supported-one-sided-inverse-rigidity` a partner drawn from anywhere
in `G` then collapses onto that subgroup and makes the lift two-sided
invertible; and its image `t_0` (resp. `s_0`) is not a unit of `R`, by
`binary-leavitt-algebra-not-directly-finite`.

**What it changes.**  `leavitt-rank-three-lift-inverse-support-thirteen`
becomes vacuous, and is now derivable without the Dykema--Heister--Juschenko
enumeration (route `support-thirteen-from-no-inverse`).  The compression
`a = e t~ e`, `b = e s~ e` named under the Attempts of
`leavitt-corner-one-sided-lift-exists` — whose only remaining gap was the
equation `ab = e` in `ker(pi_e)` — is refuted rather than merely stuck: no `b`
whatsoever completes that `a`.  And `s~` is excluded as the right factor in
`left-invertible-lift-of-s0-in-leavitt-group-algebra`.

**What it does not change.**  Kaplansky's Direct Finiteness Conjecture is open
in positive characteristic and this says nothing about it.  Nor does it refute
`leavitt-corner-one-sided-lift-exists` or
`leavitt-unit-group-algebra-not-directly-finite`: those quantify over all
pairs, and the no-go is confined to elements supported in a subgroup with
directly finite group algebra.  The useful reading is the contrapositive —
**any surviving candidate must have support generating a subgroup that is not
sofic**, which is why `openai-leavitt-unit-nonsofic` chose this group in the
first place and where the search now has to go.

## Scope

Items 1--3 are about the specific units of `leavitt-rank-three-unit-lift` and
the specific idempotent of `leavitt-corner-idempotent-unital-surjection`.  A
different additive splitting of `t_0` into units, or a different corner, is
untouched — the argument would have to be rerun on whatever subgroup that
splitting generates, and there is no reason for a general one to be virtually
free.
