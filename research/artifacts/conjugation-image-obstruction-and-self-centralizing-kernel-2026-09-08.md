# Conjugation images, and why the relation cover's kernel is different

2026-09-08.  Fifth ingestion into the torsion-free-transfer lane.  The
forwarded material arrived as a short note plus the full report; the report
is the previous four ingestions verbatim, and **only Theorem N is new**.
Everything else in it — the cover and its torsion-freeness, `(D)`, the
dummy-generator detector, `Rad_fd(E) = [E,E]`, `UT_3(Q)`, the perfect cover
`T`, the `Q`-indexed unitriangular `M`, the clock-and-shift rounding
obstruction, the rationalized kernel, the congruence groups, the amalgam `K`
and the counterclass `C_K` — is already on main and is not re-landed.

## Theorem N, re-derived

For any countable `G` take `F` free onto `G` with kernel `R`, and put

```text
A = (+)_(g in G) Z e_g,     H = A x| F,     f . e_g = e_(q(f)g).    (N1)
```

* **Torsion-free.**  If `(a,f)^m = 1` then `f^m = 1` in the free `F`, so
  `f = 1`; then `ma = 0` in the free abelian `A`, so `a = 0`.
* **Centralizer.**  Conjugation by `(a,f)` on `A` is the basis permutation
  induced by `q(f)`, which is the identity exactly when `q(f) = 1` (test on
  `e_1`).  So `C_H(A) = A x| R = A x R` and `H/C_H(A) = F/R = G`.
* **Finite generation.**  `r` free generators together with `e_1` suffice,
  since the conjugates of `e_1` are all the `e_g`.
* **MF, indeed LEF.**  Let `D_n` be balls of radius `n` on increasing finite
  subsets of the free generators, `B_n = q(D_n)`.  For a generator `x`,
  left multiplication by `q(x)` is a bijection between two equal-size subsets
  of `B_n`; extend it arbitrarily to a permutation of `B_n`.  Freeness turns
  those choices into a homomorphism `sigma_n : F -> Sym(B_n)`, and for fixed
  `f` and `g` all intermediate points eventually lie in `B_n`, so
  `sigma_n(f)g = q(f)g` eventually.  The same construction on `D_n` gives
  `tau_n : F -> Sym(D_n)` with `tau_n(f)(1) = f` eventually.  With
  `m_n -> infinity`,

```text
P_n = (Z/m_n)^(B_n) x| (Sym(B_n) x Sym(D_n)),
Phi_n(a,f) = (a|_(B_n) mod m_n, sigma_n(f), tau_n(f)),
```
  the second symmetric factor acting trivially on the base.  Finite support of
  `a` plus the eventual agreement makes `Phi_n` eventually multiplicative on
  any fixed pair, and every fixed nonidentity element is eventually detected —
  `tau_n` sees a nontrivial free part, coefficient reduction sees a nonzero
  abelian part.  Left regular representations give the operator-norm models.

  The point of doing it this way, and worth recording: **no finite quotient of
  `G` is used anywhere**.  A construction that reduced `G` would be useless,
  since the intended inputs are not residually finite.

* **A second calibration, from the report's own Theorem N section.**  For
  `g = q(f)` in the finite residual of `G`,

```text
[(0,f),(e_1,1)] = (e_g - e_1, 1) != 1,                              (N2)
```
  and every exact finite-dimensional unitary representation of `H` kills it:
  the joint character spaces of `rho(A)` are permuted through a finite
  permutation action of `G`, which `g` fixes, so `rho((0,f))` commutes with
  the scalar `rho(e_1)` on each space.  So from a finitely generated non-MF
  `G` one gets a **finitely generated** torsion-free MF group with
  `Rad_fd != 1`.  That complements
  `perfect-torsion-free-mf-group-has-no-fd-representations`, which achieves
  total collapse but is not finitely generated: one has finite generation with
  partial collapse, the other total collapse without finite generation.

## Why it does not reach (D), made precise

The report says the limitation is that `C_H(A) = A x R` is larger than `A`,
whereas the relation cover's kernel is self-centralizing.  That second half is
asserted there; it is **provable from what is already in the graph**, and the
proof is worth landing because it is exactly the structural line between the
two objects.

The Fox-type derivation `D : F -> Z[G]` with `D(x) = 0` for `x in X`,
`D(z) = 1` and `D(uv) = D(u) + q(u)D(v)` kills `[R,R]`, and

```text
D(f z f^-1 z^-1) = g - 1,      g = q(f).                            (N3)
```
So `[fbar, zbar] != 1` in `E = F/[R,R]` for **every** `g != 1`.  Since
`q(z) = 1`, the element `zbar` lies in the abelian kernel `A_E = R/[R,R]`.
Hence no element of `E` outside `A_E` centralizes `A_E`, and

```text
C_E(A_E) = A_E.                                                     (N4)
```

`free-abelianized-cover-has-nontrivial-fd-radical` already carries `(N3)`,
but states it only for `g` in the finite residual, because that is where its
own conclusion needs it.  The computation is presentation-independent and
four lines, so the route landed here reproves it rather than widening that
node's scope — the lane's own recorded lesson about not dragging in a
dependency for a clause you can reprove inline.

`(N4)` is what Theorem N does not have, and it is not a cosmetic difference:
the whole force of the relation cover is that `G` acts faithfully on its
abelian kernel, so recovering `G` costs nothing extra, whereas in `(N1)` the
free group `R` sits inside the centralizer and absorbs everything.

## Scope

Theorem N refutes a **permanence principle**, not the transfer: MF plus
torsion-freeness plus a normal free abelian subgroup does not constrain the
conjugation image at all.  `(D)` is untouched, and the self-centralizing case
is exactly what remains.  No Lean certification is asserted.
