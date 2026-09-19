---
rg: 2
id: operator-norm-restricted-burnside
kind: claim
title: Every finitely generated bounded-exponent subgroup of a norm matrix corona is finite
distinct_from:
  corona-restricted-burnside-equals-power-law-moduli: that is the established equivalence of this statement with a finite family of dimension-free matrix inequalities; this is one side of that equivalence, stated as the structural question.
  corona-commuting-torsion-lifts: that concerns commuting torsion families, where finiteness of the generated subgroup is automatic (a f.g. abelian group of exponent N is finite) and the content is exact lifting; here finiteness is the whole question and no lifting is claimed.
  finite-group-corona-tail-exactification: that assumes the group is finite and exactifies; this asks whether it is finite.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Let `Q = (prod_n M_(d_n)) / (oplus_n M_(d_n))` be a norm matrix corona. Then
every finitely generated subgroup of `U(Q)` of finite exponent is finite.

This is the structural statement that remains after stripping the program of
property `(T)`, Leavitt coefficients, traces, normalized Hilbert--Schmidt
norms, Hamming distance, corners, rank, lamps, amplification and the
compression: it mentions only a corona, a generating set and an exponent.

## Attempts

1. **Reduce to finitely many matrix inequalities.** Done, and it is the
   established `corona-restricted-burnside-equals-power-law-moduli`: for each
   `(m,N)` this statement is *equivalent* to
   `matrix-restricted-burnside-gap`. That is the live route
   (`corona-burnside-from-power-law-moduli`), and it moves the hole out of
   the corona and into a single dimension. The remaining difficulty is
   recorded there, not here.

2. **Exactify first, then quote restricted Burnside.** If a corona subgroup
   of exponent `N` could be represented by coordinatewise exact exponent-`N`
   matrix groups, Schur's theorem (a f.g. periodic linear group is finite)
   plus `restricted-burnside-finiteness` would bound each coordinate group by
   `|R(m,N)|` and finish. Exactification is available for commuting families
   (`corona-commuting-torsion-lifts`) and for representations of a group
   already known finite (`finite-group-corona-tail-exactification`), and in
   neither form does it apply. Dies at the same point as attempt 1.

3. **Look for a counterexample instead.** Nothing found, and several natural
   sources are ruled out. Exact finite-dimensional representations cannot
   witness a failure (Schur plus Mal'cev). The left regular representation of
   an infinite bounded-exponent group is infinite-dimensional, so it is no
   counterexample -- but it does show no purely C*-algebraic argument can
   assert that bounded exponent is incompatible with unitaries, which is the
   content of `universal-relations-cannot-force-proper-infiniteness`. Large
   trivial blocks and tensor amplification are defeated by
   `finite-order-unitary-has-uniform-opnorm-gap`. Normalized Hilbert--Schmidt
   or Hamming approximations of periodic groups do not become operator-norm
   approximations -- a permutation moving one point already has operator-norm
   defect of order one -- so known periodic sofic/hyperlinear phenomena do
   not refute it either.

4. **LEF free Burnside groups.** A bounded-exponent LEF group would be
   directly relevant, since exact finite local models give operator-norm
   local models. The status of LEF and soficity for the large free Burnside
   groups is delicate in exactly the range that matters here, and no theorem
   supplying the counterexample was found. This is the check to run before
   investing in a proof: a proof of `matrix-restricted-burnside-gap` may turn
   out to be equivalent to a strong LEF statement for Burnside groups.
