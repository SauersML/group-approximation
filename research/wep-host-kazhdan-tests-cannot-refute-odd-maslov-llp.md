---
rg: 2
id: wep-host-kazhdan-tests-cannot-refute-odd-maslov-llp
kind: claim
title: No Kazhdan-projection max-versus-min test over a WEP host with a genuine lift can refute the local lifting property of an odd Maslov fibre
distinct_from:
  sp4-mod3-twisted-fibres-have-llp: that is the open lifting question (TF3); this kills one whole class of refutations of it, for every WEP host including infinite-dimensional and injective ones, and decides nothing about TF3 itself.
  isw-theorem-a-has-no-data-on-sp4-lattice: that removes the finite-dimensional cocycle input of Ioana--Spaas--Wiersma Theorem A on the untwisted lattice; this is about the twisted fibres and allows arbitrary WEP hosts and infinite-dimensional representations, where no finite-dimensional input is needed.
  deligne-sector-eigenvector-certificates-die-at-induction: that kills invariant-vector certificates for sector emptiness in the matrix sector models; this kills invariant-vector certificates for failure of LLP, and the killing invariant is an invariant hypertrace rather than an induced character.
  odd-maslov-twisted-fibres-have-no-amenable-trace: that is a statement about traces on the fibre; the class-kill here needs the stronger hypertrace statement universal-cover-lattice-hypertraces-kill-z-squared, because the host representation need not be scalar on the centre and the host may have finite-dimensional quotients.
---

**ESTABLISHED (class-kill)** by route
`wep-host-kazhdan-tests-cannot-refute-odd-maslov-llp-proof`.

**Setting.**  `Gamma = Sp_4(Z)`, `Gamma~` its preimage in the universal
cover of `Sp_4(R)`, `z` the central generator.  Let `A` be a unital C-star
algebra and `u : Gamma~ -> U(A)` a unitary representation with

```text
u_z = lambda 1,      lambda^2 != 1.                               (KT0)
```

The case of interest is `A = A_alpha = C*(Gamma; alpha)`, the fibre of
`(TF3)`, with its canonical unitaries, where `lambda = omega = e^(2 pi i/3)`.
The same holds for the order-six odd fibres (`lambda = e^(+-i pi/3)`), for
every `A_theta` with `theta notin (1/2)Z/Z`, and for `C*(E_3)` cut by its
central projection onto `z = omega`.

**The test.**  A *WEP-host Kazhdan test* is a triple `(C, J, W)` where

- `C` is a C-star algebra with Lance's weak expectation property;
- `J` is a closed two-sided ideal of `C`, with quotient map `q : C -> D = C/J`;
- `W : Gamma~ -> U(C)` is a **genuine** unitary representation with
  `W_z - conj(lambda) 1 in J`.

Put `v = q o W`.  Then `U_g = u_g (x) v_g` is a unitary representation of
`Gamma~` in `A (x)_max D` with `U_z = 1`, i.e. a representation of `Gamma`.
Let `P_max` be the image in `A (x)_max D` of the Kazhdan projection of the
Kazhdan group `Gamma`.  The test **refutes LLP of `A`** if `P_max != 0`.

Examples of hosts:
- the Ioana--Spaas--Wiersma host `prod_n M_(k_n) / (+)_n M_(k_n)`;
- its infinite-dimensional version `prod_n B(H_n)` with `J = (+)_n B(H_n)`, and
  `W = (+)_n rho_n`, where the `rho_n` are genuine `t_n`-representations of
  `Gamma~` (`z -> e^(2 pi i t_n)`) with `e^(2 pi i t_n) -> conj(lambda)`, for
  instance twisted regular representations;
- every injective von Neumann algebra `C`, with any ideal `J`.

**Why the test is sound.**  If `A` had LLP, Kirchberg's theorem
(LLP `(x)` WEP: max = min) and exactness of `(x)_max` would identify
`A (x)_max D` with `(A (x)_min C)/(A (x)_min J)`.  In there `P_max` is the
image of the Kazhdan projection of `Gamma~` under `u (x) W`.  Part (i)
below shows that image is `0`.  So LLP forces `P_max = 0`, and `P_max != 0`
would refute LLP.  This is the Ioana--Spaas--Wiersma mechanism with its
finite-dimensional host replaced by any WEP host.

**Theorem.**  Assume `(KT0)`.

- **(i) Min side.**  For every C-star algebra `C` and every representation
  `W`, the Kazhdan projection of `Gamma~` maps to `0` in `A (x)_min C`.
- **(ii) Max side: the class-kill.**  For every WEP-host Kazhdan test,
  `P_max = 0`.  Equivalently, no state `psi` of `A (x)_max D` satisfies
  `psi(u_g (x) v_g) = 1` for all `g`.  So every such test returns the answer
  that LLP predicts, and none of them can refute `(TF3)`.

**Where every member dies, and the invariant.**  Suppose a member of the
class succeeds, so some `psi` has `psi(u_g (x) v_g) = 1` for all `g`.
- `psi` restricts to a `v`-invariant state on `D`.
- Through the quotient map and Lance's weak expectation, that state becomes a
  state `Phi` on `B(H)` which is Ad-invariant for the genuine lift `W`.
- `Phi(W_z) = conj(lambda)`, so `Phi(W_z^2) = conj(lambda)^2 != 1`.

This contradicts `universal-cover-lattice-hypertraces-kill-z-squared`, which
says every such invariant hypertrace has `Phi(W_z^2) = 1`. The killing
invariant is the value `Phi(W_z^2)` of an Ad-invariant hypertrace of the
host lift, which Deligne's finite residual together with Kirchberg--Brown
trace rigidity pins to `1`.

**What survives (outside the class).**

1. Hosts without a genuine lift of `v` to `C`. The operator-norm
   `1/3`-models of the flagship live here: their coordinates are only
   asymptotic representations. Soundness step (i) is then unavailable, so
   the test needs a different min-side argument.
2. Non-WEP hosts, where LLP gives no max = min identification. Either
   another soundness argument or a non-LLP proof is needed.
3. Certificates other than the projection onto `Gamma`-invariant vectors of
   `u (x) v`, such as eigenprojections of subgroups with relative (T).
   These are not covered.

The untwisted and metaplectic fibres (`lambda^2 = 1`) are untouched. There
the hypertrace bound gives no contradiction, as its sharpness example shows.
