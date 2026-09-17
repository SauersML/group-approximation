---
rg: 2
id: sp4-parabolic-radical-theorem-c-data-dies-proof
kind: route
title: Stabilizer trichotomy - free actions by CFW, central stabilizers by relative (T) on the commutator cocycle, atomic actions by finite invariant characters
target: sp4-parabolic-radical-theorem-c-data-dies
requires: []
---

**Setup.**  Fix a Borel pointwise model of `sigma`.  In the twisted group ring
of `P` over `L^0(X,T)` we have `u_g f u_g^{-1} = sigma_g(f)` and
`u_g u_h = c(g,h) u_{gh}`.  This ring is associative by the cocycle identity.
Replacing `u_g` by `b(g) u_g` with `b(g) in L^0(X,T)` changes `c` by a
coboundary.  Put `L = P/R` (`R` normal in `P`).  It is a finite-index subgroup of
`GL_2(Z)` or of `{+-1} x SL_2(Z)`, so `L_0 = L cap SL_2(Z)` is Zariski dense in
`SL_2`.

- **Siegel.**  `R` is a lattice in `Sym^2(Q^2)` with `L` acting by
  `S -> g S g^T`.  This module is irreducible for `L_0`.
- **Klingen.**  `R` is a lattice in the Heisenberg group, with centre `Z_R` of
  rank one.  `L` acts on `R/Z_R ~ Z^2` through the standard `SL_2` module and
  fixes `Z_R` pointwise (the `{+-1}` factor acts on the long root by its
  square).  So `Z_R` is central in `P`.  Lifts of two independent vectors of
  `R/Z_R` have a nontrivial commutator in `Z_R`.

**Step 0 (trichotomy).**  `x -> K_x = Stab_R(x)` is Borel, and
`K_{px} = p K_x p^{-1}`.  `Sub(R)` is countable, since `R` is finitely
generated nilpotent and every subgroup is finitely generated.  The pushforward
of `mu` is a `P`-invariant probability on a countable set, so it is carried by
finite `P`-orbits.  If the orbit of `K` is finite, `K` is normalized by a
finite-index `P_1 <= P`.  So `K (x) Q` (Siegel), or the image of `K` in
`R/Z_R (x) Q` (Klingen), is invariant under a finite-index subgroup of `L_0`,
and is therefore `0` or everything.

- **Siegel:** `K = 1` or `[R:K] < infinity`.
- **Klingen:** `K <= Z_R`, so `K = 1` or `K = mZ_R` with `m >= 1`.  Otherwise
  `K` has finite-index image and, via commutators, `K cap Z_R != 1`, so
  `[R:K] < infinity`.

Each type (`1`, central, finite index) is a conjugation-invariant property of
`K_x`, so the set where it holds is `P`-invariant.  `P` is ergodic because
`Lambda` is, so one type holds a.e.  In the central type `K_x = mZ_R` is a
single point of its orbit, so `m` is a.e. constant.

**Case (a): `K_x = 1` a.e.**  Then `Lambda` acts essentially freely and
ergodically, and `Lambda` is amenable.  ISW (arXiv:2006.01874, p. 3, verbatim):
"`H^2(Gamma,L^0(X,T))=0`, for any free ergodic p.m.p. action
`Gamma ~> (X,mu)`, if `Gamma` is an amenable group [CFW81]".  So
`c_n|Lambda` is a coboundary for every `n`.

**Case (c): `[R:K_x] < infinity` a.e.**  `Stab_Lambda(x) = Lambda cap K_x` has
finite index in `Lambda`, so every `Lambda`-orbit is finite.  An ergodic p.m.p.
action with finite orbits is a single orbit with uniform measure.  So
`X = Lambda x_0 = P x_0` is finite.

Let `P_1 = Stab_P(x_0)`, `N_1 = R cap P_1` (normal in `P_1`, finite index in
`R`) and `Lambda_1 = Lambda cap P_1 <= N_1`.  As a `Lambda`-module,
`L^0(X,T) = Coind_{Lambda_1}^{Lambda} T`.  Shapiro's lemma: the map
`[c] -> [c(.,.)(x_0)|Lambda_1]` is an isomorphism
`H^2(Lambda, L^0(X,T)) -> H^2(Lambda_1, T)`.  Evaluation at `x_0` is a cocycle
on the stabilizer, since `sigma_a f (x_0) = f(x_0)` for `a in P_1`.

Now `c'_n = c_n(.,.)(x_0)` lies in `Z^2(P_1,T)` and `c'_n -> 1` pointwise.  By
the universal coefficient theorem (`T` divisible),
`H^2(N_1,T) = Hom(H_2(N_1,Z), T)`, via evaluation on bar cycles.  So the class
of `c'_n|N_1` is a character `chi_n` of the finitely generated abelian group
`H_2(N_1,Z)`.  Each value `chi_n(a)` is a finite product of values of `c'_n`,
so `chi_n -> 1` pointwise.  Since the class extends to `P_1` and `N_1` is
normal in `P_1`, `chi_n` is invariant under the conjugation action of `P_1`.
That action factors through a finite-index subgroup `L_1` of `L`.

Rationally:

- **Siegel:** `H_2(N_1,Q) = Lambda^2(Sym^2 Q^2) = Sym^2 (x) det`.
- **Klingen:** in the LHS spectral sequence of `Z_1 -> N_1 -> Z^2`,
  `d_2 : H_2(Z^2) -> H_1(Z_1)` is nonzero, because `N_1` is non-abelian.  So
  `H_2(N_1,Q) = H_1(Z^2) (x) H_1(Z_1) = V`, the standard module.

Neither has `SL_2` invariants, so for the Zariski-dense `L_1 cap SL_2(Z)` both
invariants and coinvariants vanish.  Hence `H_2(N_1,Z)_{L_1}` is finite, and
`Hom(H_2(N_1,Z),T)^{L_1} = Hom(H_2(N_1,Z)_{L_1}, T)` is a finite set containing
`1`.  Pointwise convergence inside a finite set forces `chi_n = 1` for large
`n`.  Then `c'_n|N_1` is a coboundary, hence so is `c'_n|Lambda_1`, and by
Shapiro so is `c_n|Lambda`.

**Case (b): Klingen, `K_x = mZ_R` a.e., `m >= 1`.**  Let
`Lambda cap mZ_R = <z^k>`.  If this is trivial, `Lambda` acts freely and Case
(a) applies.  Otherwise `z^k` is central in `P` and acts trivially on `X`.

1. *Commutator cocycle.*  Both `u_{z^k} u_g` and `u_g u_{z^k}` are in
   `L^0 u_{z^k g}`, so `u_{z^k} u_g u_{z^k}^{-1} = gamma_n(g) u_g` with
   `gamma_n(g) = c_n(z^k,g) c_n(g,z^k)^{-1}`.  `Ad u_{z^k}` is multiplicative
   and fixes `L^0` (`sigma_{z^k} = id`).  Hence
   `gamma_n(gh) = gamma_n(g) sigma_g(gamma_n(h))`, a 1-cocycle on `P`.
2. *Relative (T).*  `pi_n(g) f = gamma_n(g) sigma_g(f)` is a unitary
   representation of `P` on `L^2(X)`, and
   `||pi_n(g)1 - 1||_2 = ||gamma_n(g) - 1||_2 -> 0` for every `g`.  Let
   `J = {n : gamma_n|Lambda` not a coboundary`}`.  Suppose `J` is infinite.
   Then `(+)_{n in J} pi_n` has almost invariant vectors, so it has a nonzero
   `Lambda`-invariant vector (ISW's definition, arXiv:2006.01874 p. 2: "any
   unitary representation of `Gamma` with almost invariant vectors has a
   non-zero `Lambda`-invariant vector").  Some component `xi != 0` in `pi_n`,
   `n in J`, is `Lambda`-invariant: `gamma_n(l) sigma_l(xi) = xi`.  So `|xi|` is
   `sigma|Lambda`-invariant, hence a nonzero constant by ergodicity.  Then
   `eta = xi/|xi|` gives `gamma_n(l) = eta sigma_l(eta)^{-1}`, contradicting
   `n in J`.  So `J` is finite.
3. *Centralize.*  For `n` not in `J` put `w = eta^{-1} u_{z^k}`.  Then
   `w u_l w^{-1} = eta^{-1} gamma_n(l) sigma_l(eta) u_l = u_l` for `l in Lambda`,
   and `w` commutes with `L^0`.  Choose a section `s : Lambda/<z^k> -> Lambda`,
   write `l = s(q) z^{kj}`, and set `U_l = u_{s(q)} w^j in L^0 u_l`.
   - Since `w` is central and `s(q)s(q') = s(qq') z^{k a(q,q')}`,
     `U_l U_{l'} = F_n(q,q') U_{l l'}` with `F_n(q,q') in L^0(X,T)` depending
     only on `(q,q')`.
   - Associativity makes `F_n` a 2-cocycle of `Lambda/<z^k>` with coefficients
     `L^0(X,T)`.
4. *Descend.*  `Lambda/<z^k>` is amenable and acts freely (the
   `Lambda`-stabilizers are exactly `<z^k>`) and ergodically.  By the CFW
   statement quoted in Case (a), `F_n = d beta_n`.  So the cocycle of `U`,
   which is cohomologous to `c_n|Lambda`, is a coboundary.

In all three cases `c_n|Lambda` is a coboundary for all large `n`, which is
`(RTC1)`.

**Consequence 1 (torsion residue).**

- If `(P,Lambda)` has relative (T), its image in `L` has relative (T) in the
  virtually free, hence a-T-menable, group `L`, so it is finite.  Finite
  subgroups of `GL_2(Z)` and of `{+-1} x SL_2(Z)` have order at most `12`.
- `(P, Lambda cap R)` inherits relative (T).  If `Lambda cap R` is ergodic,
  `(RTC1)` applies to it, and `cor o res = d` shows `[c_n|Lambda]` is `d`-torsion
  for large `n`.

The case where `Lambda cap R` is non-ergodic (at most `d` ergodic components)
is not treated here.
