---
rg: 2
id: bounded-area-commuting-conjugator-localization
kind: claim
title: In a torsion-free finitely presented group, an element that commutes with h by a relation of bounded area lies in <h> times a bounded ball of the centralizer
distinct_from:
  infinite-chromatic-commutator-code-kills-mf-mark: that uses bounded area to colour a code graph by unitary cells; this is a purely combinatorial localization of the commuting element itself, with no representation.
  lifted-thompson-t-conjugate-template-codes-have-bounded-cliques: that is the application to conjugate templates in T-bar; this is the group-independent localization it uses.
---

**Statement.**  Let `Gamma = <S | R>` be a finite presentation of a
torsion-free group, let `M` be the largest length of a relator, and let `h`
be a word with `h != 1` in `Gamma`.  If `y` is any word (not necessarily
reduced) with

```text
Area_R(y h y^(-1) h^(-1)) <= A,
```

then in `Gamma`

```text
y = h^n g,   n in Z,   g in C_Gamma(h),   |g|_S <= K := A M + 2|h|.     (LOC)
```

So the set of elements `y` with `Area([y,h]) <= A` is contained in
`<h> T_0` with `T_0 = C_Gamma(h) ∩ B_S(K)` finite.

**Why it matters.**  Bounded-area commutator codes
(`infinite-chromatic-commutator-code-kills-mf-mark`) ask for long words that
commute with a fixed word at bounded cost.  (LOC) says that at bounded cost
the commuting element is determined, up to powers of `h`, by finitely many
choices.  Any conjugacy invariant that separates the powers `h^n t` then
makes the set finite.  That is the step used in
`lifted-thompson-t-conjugate-template-codes-have-bounded-cliques`.

Proof: `bounded-area-commuting-conjugator-localization-proof`
(van Kampen diagram, glued to an annulus, mapped to the quotient
`<h>\X` of the Cayley complex; point preimages of free edges are closed
curves, essential ones would kill `h` in `pi_1 = <h>`).
