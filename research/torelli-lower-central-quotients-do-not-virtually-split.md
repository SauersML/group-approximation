---
rg: 2
id: torelli-lower-central-quotients-do-not-virtually-split
kind: claim
title: For g >= 3 and c >= 2 the Torelli lower-central quotient Mod(S_g)/T_g[c+1] does not split over any finite-index subgroup of Sp_2g(Z), even modulo a finite subgroup
distinct_from:
  torelli-lower-central-quotients-are-not-residually-finite: that proves the quotients are not residually finite, using this node plus Borel and Deligne; this is the elementary non-splitting statement, which needs only Nowak's non-linearity theorem and superrigidity.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that is a central extension of Sp_2n(Z) by Z; this is an extension of Sp_2g(Z) by a finitely generated nilpotent group coming from the Torelli group.
artifacts:
  - research/artifacts/gq-bh-bh-free-38-torelli-quotients.md
---

**ESTABLISHED** (lane proof, elementary given the cited inputs; not reviewed; no
priority claimed).

**Notation** (Nowak, arXiv:2609.12196v1, TeX l.176–178). `T_g` is the Torelli
group, `T_g[j]` its lower central series (`T_g[1] = T_g`), and
`Q_{g,c} = Mod(S_g)/T_g[c+1]`, `N_{g,c} = T_g/T_g[c+1]`. So
`1 -> N_{g,c} -> Q_{g,c} -> Sp_2g(Z) -> 1`, and `N_{g,c}` is finitely generated
nilpotent (Johnson; Nowak Theorem A, l.193).

**Statement.** Let `g >= 3` and `c >= 2`. There is no pair `(Q', Sigma)` with
`Q' <= Q_{g,c}` of finite index, `Sigma <= Q'`, `Sigma ∩ N_{g,c}` finite and
the image of `Sigma` in `Sp_2g(Z)` of finite index. In particular the extension
does not virtually split.

**Proof.** Suppose such `Sigma` exists. Let `tau` be the torsion subgroup of
`N = N_{g,c}`. It is finite and characteristic, hence normal in `Q_{g,c}`. Then
`Sigma ∩ N ⊆ tau`, and in `Q'' = N·Sigma / tau` (finite index in
`Q_{g,c}/tau`) the image `Sigma-bar` of `Sigma` meets `N/tau` trivially. So
`Q'' = (N/tau) ⋊ Sigma-bar` with `Sigma-bar ≅ Lambda`, where `Lambda` is the
finite-index image in `Sp_2g(Z)`.

1. **Malcev.** `N/tau` is torsion-free, so the Malcev map
   `j: N/tau -> N_c(Q)` is injective. Here `N_c` is the rational unipotent
   completion, with Lie algebra `t_g/t_g[c+1]` (Nowak Theorem `thm:malcev`,
   l.2179). Conjugation gives a homomorphism `a: Lambda -> Aut(N_c)(Q)`, a
   linear algebraic group.
2. **Superrigidity.** By Nowak Theorem `thm:arithmeticextension`(ii) (l.2345:
   Margulis virtual algebraic extension for `Sp_2g(Z)`, g >= 3), there are a
   finite-index `Lambda' <= Lambda` and an algebraic `alpha: Sp_2g,C -> Aut(N_c)_C`
   with `a = alpha` on `Lambda'`.
3. **A faithful-mod-finite representation.** In the linear algebraic group
   `N_c ⋊_alpha Sp_2g`, the map `(n, lambda) -> (j(n), lambda)` on
   `(N/tau) ⋊ Lambda'` is an injective homomorphism. Let `Q_1` be the preimage of
   `(N/tau) ⋊ Lambda'` in `N·Sigma`, a finite-index subgroup of `Q_{g,c}`.
   Composing `Q_1 -> (N/tau) ⋊ Lambda'` with that map gives a finite-dimensional
   complex representation of `Q_1` whose kernel lies in `tau`, which is finite.
   Inducing it to `Q_{g,c}` gives a representation whose kernel is the core of
   that kernel, which is also finite.
4. **Contradiction.** This contradicts Nowak's Theorem D (l.274): for
   `g >= 3, c >= 2`, every homomorphism `Q_{g,c} -> GL_d(C)` has infinite kernel.

**Scope.** The case `c = 1` is not covered: `Q_{g,1}/B ≅ Mod/K_g` is virtually
split (Morita's embedding in `(1/2)Λ^3H ⋊ Sp`), where `B = K_g/[T_g,T_g]` is
Johnson's finite 2-group. Whether `Q_{g,1}` itself virtually splits is not
addressed here.

**Inputs, not re-derived here:** Nowak's Theorem D (read at source) and the
superrigidity statement exactly as Nowak states it (his Theorem
`thm:arithmeticextension`, citing Margulis Ch. VIII Thm B and Church–Farb).
