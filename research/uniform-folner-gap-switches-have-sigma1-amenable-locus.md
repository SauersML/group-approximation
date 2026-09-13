---
rg: 2
id: uniform-folner-gap-switches-have-sigma1-amenable-locus
kind: claim
title: A family whose non-amenable members fail the Følner condition at one fixed scale has a Sigma-zero-one amenable locus
distinct_from:
  finite-graphs-of-amenable-groups-have-sigma1-locus: that classifies one construction class, finite Bass-Serre assemblies over amenable vertices; this is a quantitative screen for any computable family, with no restriction on how the groups are built, and it recovers the Sigma-zero-one conclusion whenever the free witnesses are short words.
  amenable-base-l-presentations-have-recursive-locus: that proves a recursive locus for one syntax; this proves only Sigma-zero-one, but for every family whose non-amenable members carry free subgroups or free quotients on words of bounded length.
  recursive-amenable-classes-have-uniform-folner-bounds: that is the imported semi-decision of Følner sets at a fixed scale; this applies it to switch families and turns it into a design constraint for hardness proofs.
---

**ESTABLISHED** by `uniform-folner-gap-switches-sigma1-amenable-locus-proof`.

Let `e -> P_e = <X_e | R_e>` be a computable family of finite presentations. The
same argument works for recursive presentations given by indices. Say `Ω` is an
`n`-Følner set when `|Ω \ xΩ| <= |Ω|/n` for every `x in X_e`.

**Theorem.** Suppose there is `n*` such that

```text
(UG)  no non-amenable P_e admits an n*-Følner set with respect to X_e.
```

Then

```text
{ e : P_e amenable } = { e : P_e admits an n*-Følner set }   is Sigma^0_1.   (UG0)
```

**Two sufficient conditions for (UG)**, each with `n* = 4L`:
- **(UG1) short free subgroups.** Every non-amenable `P_e` contains words
  `u_e, v_e` of length at most `L` that freely generate a free group of rank two.
- **(UG2) short free quotients.** Every non-amenable `P_e` surjects onto
  `F(a,b)` so that `a` and `b` are images of words of length at most `L`.

**Recovered screens.**
- `finitely-generated-centralizer-switches-are-sigma1`: its free witness
  `<t, a t a^-1>`, with `a` a presentation generator outside the centralized
  subgroup, is (UG1) with `L = 3`.
- The raw substitution simulator of `amenable-base-l-presentations-have-recursive-locus`
  with two or more letters kills `X_e` onto a free group: (UG2) with `L = 1`.

## Consequence: hardness needs vanishing gaps

By `(UG0)`, a reduction proving
`amenability-of-finite-presentations-is-pi1-hard` or the completeness root must
violate (UG) at *every* scale. For each `n`, some non-amenable output must admit
an `n`-Følner set. Equivalently:
- the isoperimetric constants of the non-amenable outputs must tend to zero along
  the family;
- every free subgroup or free quotient of them must be generated only by words of
  unbounded length;
- no fixed forbidden seed may be attached through words of bounded length.

This is a constraint on *every* construction, not on one syntax. It is consistent
with the recursive two-generator switch of
`shift-raag-family-classifies-amenability`, whose free witness `<a, a^(s^j)>` has
`j` equal to the least missing index, which is unbounded along the family.

No priority is claimed: this is an elementary consequence of Cavaleri's
Corollary 3.4 and coset averaging.
