---
rg: 2
id: bounded-degree-partial-burnside-reps-factor-through-burnside
kind: claim
title: In each fixed degree, representations satisfying the exponent law on short words factor through the free Burnside group, and a degree-uniform radius is exactly the local restricted Burnside principle
distinct_from:
  local-restricted-burnside-iff-partial-burnside-finite-quotients: that reformulates the local principle through all finite quotients of a partial Burnside group; this proves the principle for linear images of each fixed degree and identifies the full principle with uniformity of the degree-wise radius.
  bounded-dimension-microstates-bounded-exponent-group-is-finite: that assumes a group of finite exponent with approximate microstates of bounded dimension; this assumes the exponent law only on words of bounded length, for exact representations.
  large-odd-exponent-local-restricted-burnside: that is the open principle at a large odd exponent; this settles its fixed-degree linear case and shows that the open content is exactly the growth of the radius with the degree.
---

**ESTABLISHED** through `bounded-degree-partial-burnside-noetherian-proof`.

**Setting.** Fix `m, N >= 2` and the free group `F = F_m` on `x_1, ..., x_m`.
For `R >= 1` and `d >= 1` put

```text
X_R(d) = { rho in Hom(F, GL_d(C)) : rho(h)^N = 1 for every h in F with 1 <= |h| <= R },
```

with `|h|` the reduced word length. `Hom(B(m,N), GL_d(C))` is the subset where
`rho(g)^N = 1` for every `g in F`. `LRB(m,N)` and the partial Burnside groups
`Π_R(m,N)` are as in `local-restricted-burnside-iff-partial-burnside-finite-quotients`.

**Statement.**
1. **Fixed-degree stabilization.** For every `d` there is a least radius
   `R_0(m,N,d) < infinity` such that `X_R(d) = Hom(B(m,N), GL_d(C))` for all
   `R >= R_0(m,N,d)`.
2. **Bounded images.** For `rho in X_R(d)` with `R >= R_0(m,N,d)`, the image
   `rho(F)` is finite, has exponent dividing `N`, and has order at most
   `f(d) N^d`, where `f` is the function of Jordan's theorem.
3. **Uniformity is the local principle.** `LRB(m,N)` holds if and only if
   `sup_d R_0(m,N,d) < infinity`.

## Consequences

- **Linear refutations need growing degree.** Attempt 4 of
  `large-odd-exponent-local-restricted-burnside` observes that an infinite
  `m`-generated linear group whose words of length `<= R` satisfy `h^N = 1`
  refutes `LRB(R, C)` for every `C`, and that the uniform Tits alternative
  *suggests* such groups need degree tending to infinity with `R`. Clause 2
  proves this: in degree `d` no infinite image exists once `R >= R_0(m,N,d)`, so
  a linear refutation at radius `R` lives in a degree `d` with
  `R_0(m,N,d) > R`.
- **The exact dimension-free statement.** For a large odd exponent, the route
  `non-rf-hyperbolic-group-via-local-restricted-burnside`, and every
  exact-model version of the finiteness route into `nonsofic-hyperbolic-group`,
  needs the radius at which the exponent law on short words forces the full
  Burnside law to be bounded independently of the degree. Clause 3 shows that
  this uniformity is equivalent to `LRB(m,N)`, so it is at least as hard as a
  non-residually-finite hyperbolic group (clause 5 of the LRB reformulation).
  Noetherianity gives each `R_0(m,N,d)` but no bound on it, and carries no
  information across degrees.
- **Why bounded dimension never decides the Hilbert--Schmidt route.** The same
  degree dependence appears on the approximate side:
  `bounded-dimension-microstates-bounded-exponent-group-is-finite` settles
  bounded dimensions, and a counterexample to
  `hyperlinear-fg-bounded-exponent-groups-are-finite` needs unbounded
  dimensions. Clauses 1 and 3 show that already for exact models the passage to
  unbounded degree is precisely where the open principle sits.

## Trust surface

- **Schur's theorem** (1911), cited as in
  `bounded-dimension-microstates-bounded-exponent-group-is-finite`. Text pinned
  from the Wikipedia "Burnside problem" wikitext, fetched on MSI 2026-09-13:
  "[[Issai Schur]] had shown in 1911 that any finitely generated periodic group
  that was a subgroup of the group of invertible ''n'' × ''n'' complex matrices
  was finite".
- **Jordan's theorem.** Text pinned from the Wikipedia "Jordan–Schur theorem"
  wikitext, fetched on MSI 2026-09-13: "there is a function ''ƒ''(''n'') such
  that given a finite subgroup ''G'' of the group GL(''n'', '''C''') of
  invertible ''n''-by-''n'' complex matrices, there is a subgroup ''H'' of ''G''
  with the following properties: ''H'' is abelian. ''H'' is a normal subgroup of
  ''G''. The index of ''H'' in ''G'' satisfies (''G'' : ''H'') ≤ ''ƒ''(''n'')."
  The primary sources were not read.
- **Malcev's theorem**, through `finitely-generated-linear-groups-are-residually-finite`.
- **Standard facts, not re-read:** the Hilbert basis theorem, and simultaneous
  diagonalization of a commuting family of complex matrices of finite order.

No novelty is claimed; clauses 1 and 2 are a standard Noetherian argument.
