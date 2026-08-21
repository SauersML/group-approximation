---
rg: 2
id: hnn-over-codense-kazhdan-subgroup-not-hyperlinear
kind: claim
title: Centralizing a co-dense Kazhdan subgroup of a stable group by a stable letter gives a nonhyperlinear HNN extension
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  pauli-lamplighter-over-stable-codense-kazhdan-pair: that hangs a Pauli group on the cosets and marks the central involution; this marks the commutator of the stable letter with one element of the big group and needs no Pauli structure, no prototype relator and no extra generators, so it supersedes that theorem under the same hypotheses.
  hs-stability-forces-nonhyperlinear-central-extension: Dogon--Vigdorovich consume stability of a (T;FD) group through a central Z-extension and asymptotically projective representations; this consumes stability of a host through a co-dense (T;FD) subgroup and an HNN extension, with a direct microstate argument.
  amenable-edge-hnn-preserves-hyperlinearity: that is the positive permanence theorem for HNN extensions over amenable associated subgroups; this is the negative statement for an associated subgroup that is Kazhdan and co-dense, conditional on stability of the base.
---

**Data.**  `C <= A` finitely generated groups; `C` has Lubotzky--Zimmer
property (T;FD) with Kazhdan constant `kappa` for a finite generating set
`S_C`; the pair is finite-dimensionally co-dense
(`two-transitive-infinite-action-is-finite-dimensionally-codense`):
`pi^C = pi^A` for every finite-dimensional unitary representation `pi` of
`A`; `a_1 in A \ C`.  Let

```text
G = < A, t | t c t^(-1) = c  (c in S_C) >,                         (HC1)
```

the HNN extension of `A` with both associated subgroups `C` and identity
map.  By Britton's lemma `w := [t, a_1] != 1` in `G`.

**Theorem.**  Let `U` be a finite-dimensional unitary tuple for the
generators of `G` with defect `<= tau` on the relators of `A`, the
relators `[t, c]` (`c in S_C`), and suppose the `A`-part of `U` is within
`eta` on generators of an exact finite-dimensional unitary representation
`rho` of `A`.  Then

```text
||U(w) - I||_2 <= C_0 ( (tau + eta)/kappa + |a_1| eta ),                (HC2)
```

with `C_0` depending only on the word lengths of `S_C` in the generators
of `A`.

**Corollary.**  If `A` is flexibly Hilbert--Schmidt stable (Dogon--Vigdorovich's
notion, Definition 1.2 of arXiv:2506.20843), then `G` is not hyperlinear.

*Proof of the theorem.*  Put `g = U(t)`.  For `c in S_C` the relator gives
`||U(c) g U(c)^* - g||_2 <= tau`, and `||U(c) - rho(c)||_2 <= |c|_A eta`, so
`||rho(c) g rho(c)^* - g||_2 <= tau + 2|c|_A eta`.  Apply (T;FD) to the
finite-dimensional unitary representation `Ad rho|_C` of `C` on
`(M_d, <,>_HS)`: with `E` the projection onto the invariant vectors, which
is the conditional expectation onto the commutant `rho(C)'`,
`||g - Eg||_2 <= (tau + 2 max|c|_A eta)/kappa`.  By co-density applied to
`pi = Ad rho`, `rho(C)' = rho(A)'`, so `Eg` commutes with `rho(a_1)`.
Hence `g U(a_1) g^* - U(a_1)` is within `O(||g - Eg||_2 + |a_1| eta)` of
`Eg rho(a_1)(Eg)^* - rho(a_1) = rho(a_1)((Eg)(Eg)^* - I)`, which is within
`2||g - Eg||_2` of zero.  So `||g U(a_1) g^* U(a_1)^* - I||_2` is bounded as
in `(HC2)`. ∎

*Proof of the corollary.*  If `G` were hyperlinear there would be tuples
`U_n` with defect tending to zero and `tr U_n(w) -> 0` since `w != 1`.
Flexible stability of `A` gives exact representations on slightly larger
spaces; padding `U_n` by the identity on the extra corner changes defect
and traces by `o(1)`, and unitarity forces the off-corner part of the
exact representation to be small, so the padded tuple is within
`eta_n -> 0` of an exact representation.  Then `(HC2)` gives
`tr U_n(w) -> 1`. ∎

**Remarks.**
1. With `tau = eta = 0` the theorem says every finite-dimensional unitary
   representation of `G` kills `w`; so `G` is never maximally almost
   periodic, and nothing is claimed about exact representations beyond
   that.
2. The contrapositive is a disproof route for stability: if the HNN
   extension `G` is hyperlinear, `A` is not flexibly HS-stable.  For
   `A = SL_2(Z[1/pq])`, `C = SL_2(Z[1/p])`
   (`sl2-s-arithmetic-pair-is-codense-kazhdan`), hyperlinearity of
   `SL_2(Z[1/pq]) *_C (C x Z)` would refute the stability of
   `SL_2(Z[1/pq])`.
3. Finite-dimensionality enters only through co-density, which fails for
   the quasi-regular representation `l^2(A/C)`, exactly as it must by
   `regular-trace-blocks-exact-local-predicate-return`.
4. The same argument with an asymptotic representation in place of `rho`
   would need co-density for tracial representations into ultraproducts;
   that version is equivalent to the conclusion (take the regular
   representation of `G` itself), so stability cannot be dropped.

**The `(tau)` form.**  The proof uses (T;FD) of `C` only through the
conjugation representations `Ad rho|_C` for the finite-dimensional
representations `rho` of `A` that stability produces.  So it suffices that
`C` have a uniform spectral gap on those: for instance property `(tau)` of
`C` with respect to a family of finite quotients through which all
finite-dimensional representations of `A` factor.  With
`A = SL_2(Z[1/p])`, `C = SL_2(Z)`
(`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`) this gives:

> if `SL_2(Z[1/p])` is flexibly HS-stable, then
> `G_p = <SL_2(Z[1/p]), t | [t, SL_2(Z)] = 1>` is not hyperlinear.

For `p = 2` the hypothesis is exactly Dogon--Vigdorovich's
`iwahori-local-global-defect-question`, so the goal now has two routes from
that one question: their finite central extension of `SL_2(Z[1/2])` and this
HNN extension of it.

**The explicit instance.**

```text
G_(p,q) = < SL_2(Z[1/pq]), t | [t, SL_2(Z[1/p])] = 1 >,              (HC3)
```

finitely presented, with `w = [t, diag(q, q^(-1))]`.  It is nonhyperlinear
as soon as `SL_2(Z[1/pq])` is flexibly HS-stable (`sl2-z-inverse-pq-is-hs-stable`).
