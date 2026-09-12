---
rg: 2
id: flexibly-but-not-strictly-hs-stable-group-exists
kind: claim
title: Some finitely generated group is flexibly Hilbert--Schmidt stable but not Hilbert--Schmidt stable
distinct_from:
  sl2-half-explicit-strict-flexible-separation: that separates strict from flexible repair for one sequence of PSL_2(Z[1/2]); this asks for a group on which every asymptotic representation is flexibly repairable while some is not strictly repairable.
  amenable-flexible-hs-stability-is-strict-hs-stability: that proves the two notions agree when the maximal almost periodic quotient is amenable; this asks for a group where they differ, which that theorem confines to non-amenable maximal almost periodic quotients.
  sln-z-flexibly-hs-stable: that is flexible stability of one integral lattice; since strict stability fails for every infinite hyperlinear Kazhdan group, a proof of that claim for a Kazhdan lattice would also prove this one.
---

**OPEN.** Find a finitely generated group `Γ` that is flexibly HS-stable in
Dogon arXiv:2211.10492v3 Definition 1.2 but not HS-stable, i.e. fails that
definition with `D_n = d_n` (Dogon's footnote 1).

**Source.** Dogon, p. 3, after Theorem 1.3, verbatim: "Thus, deciding flexible
HS-stability in this scenario is extremely interesting. With that said, there
is no known example of a group that is flexibly HS-stable, but not HS-stable."

**Why it sits on the stability routes.** Strict stability is excluded for every
infinite hyperlinear Kazhdan group
(`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`), and for
`PSL_2(Z[1/2])` by `sl2-half-explicit-strict-flexible-separation`. So flexible
HS-stability of `Sp_2g(Z)` (`non-hyperlinear-from-sp2g-flexible-hs-stability`)
or of `SL_2(Z[1/2])` (`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`)
would each be an instance of this claim.

## Attempts

**2026-09-12, lane `hs-flexible-not-strict-example`.**

1. **Amenable groups: excluded.** The directive's first candidate was an
   amenable group where strict repair fails by dimension parity and flexible
   repair works. There is none:
   `amenable-flexible-hs-stability-is-strict-hs-stability` proves (a) ⇔ (b)
   for every finitely generated group with amenable maximal almost periodic
   quotient. Padding with trivial summands absorbs parity, and Jung
   tubularity supplies the same-dimensional conjugacy.
2. **Sequence-level localization.**
   `injective-limit-trace-flexible-hs-repair-is-strict`: every sequence that
   is flexibly but not strictly repairable along `ω` has a limit trace whose
   GNS algebra is non-injective. The one explicit separating sequence on main,
   for `PSL_2(Z[1/2])`, therefore has non-injective limit traces. For a
   hyperlinear candidate, the example must be residually finite
   (`hyperlinear-flexibly-hs-stable-group-is-residually-finite`) and
   non-amenable.
3. **Regimes already closed by published flexible instability**, as listed by
   Dogon p. 3:
   - `SL_2(Z) ⋉ Z^2`, not flexibly HS-stable (Ioana--Spaas--Wiersma, Dogon's [28]);
   - `F_m × F_k`, not flexibly HS-stable (Ioana, Dogon's [31]);
   - finitely generated hyperlinear groups that are not residually finite
     (Becker--Lubotzky, Dogon's [7]).
4. **Regimes with no separation available.** Dogon p. 3 lists as
   "(flexibly) HS-stable":
   - finitely generated virtually nilpotent groups, certain lamplighter groups
     and `BS(1,n)`;
   - certain one-relator groups and virtually free groups;
   - direct products with HS-stable amenable groups.

   Hadwin--Shulman Theorem 1 adds free products of matricially stable groups.
   By Dogon's sentence above, none of these is a known separation.
5. **Remaining regime: rigid, non-amenable, residually finite groups.** Two
   families already carry strict failure:
   - infinite hyperlinear Kazhdan groups, where flexible stability equals weak
     ucp-stability (`kazhdan-weak-ucp-stability-is-flexible-stability`);
   - `PSL_2(Z[1/2])`.

   For `Sp_2g(Z)` and `SL_2(Z[1/2])`, flexible stability already yields a
   non-hyperlinear group, so an example there is at least as hard as that
   goal (`sp2g-flexible-stability-forces-twisted-non-ce`). For `SL_n(Z)`,
   `n >= 3`, no such implication is on main, but flexible stability is the
   open question of Becker--Lubotzky (`sln-z-flexibly-hs-stable`).
6. **Not attempted: upgrading very flexible stability.** Fournier-Facio--Willett
   arXiv:2603.18456v2 give compression approximation with no dimension-ratio
   condition for LLP + property FD groups (recorded in
   `research/artifacts/nonhyperlinear-literature-delta-parallel-2026-08-31.md`,
   §2). Two things would give an example here:
   - a ratio-one upgrade for one non-amenable group in their class;
   - a Weil-type strict obstruction for the same group.

   Neither is known to this lane. By item 2, the needed strict obstruction
   must sit on a non-injective trace, such as the regular trace.
