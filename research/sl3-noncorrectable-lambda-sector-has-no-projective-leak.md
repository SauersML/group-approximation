---
rg: 2
id: sl3-noncorrectable-lambda-sector-has-no-projective-leak
kind: claim
title: Uniformly noncorrectable canonical SL3 lattice microstates have no projective arithmetic leak
distinct_from:
  sl3-odd-correctable-sector-has-uniform-projective-modulus: that proves projective transfer after correction to congruence representations of level coprime to p; this asks for the complementary sector uniformly far from every exact finite-dimensional lattice representation.
  fixed-projective-gap-forces-primary-congruence-mass: that constrains the p-primary mass inside an available exact correction; this applies where no such correction exists at all.
  sl3-canonical-double-has-a-correctable-vertex: that would remove this sector by proving at least one vertex is correctable; this asks directly for absence of a projective leak without first correcting the vertex.
---

OPEN.  Let `rho_n` be canonical-character normalized-HS microstates of

```text
Gamma=SL_3(Z[1/p])
```

whose restrictions to `Lambda=SL_3(Z)` stay at a uniform positive
generator distance from every exact finite-dimensional representation of
`Lambda`.  If unitaries `U_n` satisfy

```text
sum_(c in S_Lambda)
 (1-|tr([U_n,rho_n(c)])|^2)->0,                         (UNC1)
```

then

```text
1-|tr([U_n,rho_n(h)])|^2->0.                            (UNC2)
```

This is the exact sector not touched by congruence conductor, parahoric
branching, or shell-PVM arguments.  Proving it directly, or proving that a
canonical arithmetic microstate always has a correctable lattice vertex,
is independently necessary for full
`projective-commutant-transfer-for-arithmetic-pair`.

## Attempts

Property `(T)` does not directly control this sector: the adjoint maps of a
normalized-HS microstate are still only an approximate representation, so
the Kazhdan projection cannot be applied before an exactification step.
Correcting that adjoint representation is precisely the special stability
statement already isolated in the parent PRCC claim, and general HS
stability of `SL_3(Z)` is false.  The attack is therefore deferred until one
uses an arithmetic denominator relation to exactify the adjoint lift or
proves the alternative one-correctable-vertex theorem.

The exact remaining correction hypothesis is now narrower.  By
`sl3-regular-projective-correction-is-inner-adjoint-stability`,

```text
||Ad(U)-Ad(V)||_(2,End(M_d))^2
 =2(1-|tr_d(U*V)|^2),                                  (UNC3)
```

so projective correction of the canonical lattice tuple is equivalent to
HS correction of its adjoint tuple **within inner conjugation
representations**.  The adjoint character is still regular, because
`tr(Ad(rho(g)))=|tr(rho(g))|^2`.  Arbitrary HS correction of the adjoint
tuple is insufficient: it need not remain inner and normalized-HS closeness
of superoperators does not control their action on the selected vector
`U_n`.

`sl3-rigidity-stops-before-inner-adjoint-correction`
checks the primary literature boundary.  Strict and local HS stability of
`SL_3(Z)` are false (Becker--Lubotzky; Fournier-Facio--Gerasimova--Spaas),
but those existential bad challenges do not decide this restricted class.
Dogon--Vigdorovich's positive character-rigidity theorem gives hyperfinite
HS stability only; the regular character generates the nonamenable factor
`L(SL_3(Z))` and lies outside its hypothesis.  Thus character rigidity does
not correct this sector.  The remaining named condition is regular
inner-adjoint HS stability, strictly narrower than full flexible stability
but currently open.  A direct denominator argument could still prove
`(UNC2)` without it.

The direct root/relative-`(T)` bypass now has two exact fences.

- `one-root-p3-denominator-fragment-has-finite-regular-leaks` uses
  separating finite quotients of

  ```text
  <a,h | h a h^(-1)=a^9>=BS(1,9)
  ```

  and the exact substitution `t=a`.  The root restriction has canonical
  limiting trace, `[t,a]=1`, but `1-|tr([t,h])|^2=1`.  Hence no one-root
  scaling or trace-square argument can work, even in exact finite matrices.
- `full-sl3-root-package-has-an-exact-tracial-hnn-leak` keeps all six roots,
  all denominator conjugacies and the whole lattice simultaneously in the
  regular factor of

  ```text
  <Gamma,t | [t,Lambda]=1>.
  ```

  There `t` centralizes `Lambda` exactly while its commutator with `h` has
  canonical trace zero.  Thus property `(T)`, relative property `(T)`, root
  identities and finite-tracial positivity cannot imply `(UNC2)` as a
  universal tracial inequality.  This is not a matrix countermodel because
  Connes embeddability of that factor is unknown.

Therefore any correction-free proof must use a genuinely joint,
finite-dimensional/embeddability-sensitive incidence among multiple roots.
The known p-three exact-face flux proposal has that shape, but its flatness
and transport-dictionary seams remain open; it cannot presently be imported
into the uniformly noncorrectable sector.
