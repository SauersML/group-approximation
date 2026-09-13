---
rg: 2
id: sp2g-universal-cover-lattice-is-operator-hs-stable
kind: claim
title: For g >= 3 the preimage of Sp_2g(Z) in the universal cover of Sp_2g(R) is operator-HS-stable (BDL Conjecture 1.8 for this lattice)
distinct_from:
  bdl-deligne-type-two-norm-inapproximability: that imports the general Conjecture 1.8 of Bachner--Dogon--Lubotzky as a stated conjecture; this is its single instance for the universal-cover lattice at genus at least three, where property [T_2] is established.
  sp2g-z-flexibly-hs-stable: that is flexible normalized-HS stability of the residually finite base for HS-asymptotic homomorphisms; this starts from operator-norm asymptotic homomorphisms of the non-residually-finite cover and asks for same-dimension HS rounding.
  blsw-real-lattice-frobenius-stability: that is rounding in the unnormalized Frobenius norm, where corrections are submultiplicative; this is rounding from operator-norm input to normalized-HS output, where they are not.
---

**OPEN.** Let `g >= 3`, `Gamma~ = Gamma~_g` the preimage of `Sp_(2g)(Z)` in the universal cover of
`Sp_(2g)(R)`, `z` the covering generator. Every operator-norm asymptotic homomorphism
`phi_k : Gamma~ -> U(d_k)` admits genuine homomorphisms `psi_k : Gamma~ -> U(d_k)` with

```text
lim_k ||phi_k(x) - psi_k(x)||_HS = 0        for every x in Gamma~.          (OHS1)
```

**Why this instance.** `Gamma~` is finitely generated and has `[T_2]` (BLSW Theorem 2.10, in
`blsw-real-lattice-frobenius-stability`). So `(OHS1)` is Conjecture 1.8 of Bachner--Dogon--Lubotzky,
arXiv:2508.17392v3, p. 3, for `Gamma~`. The finite covers `Gamma_n = Gamma~/<z^n>` are *not*
instances: `H^2(Gamma_n; R) = H^2(Sp_(2g)(Z); R) != 0` (BLSW p. 3), so they fail `[T_2]`.

**Payoff.** `deligne-sp2g-covers-not-mf-from-operator-hs-stability` derives from `(OHS1)` that
every finite Deligne cover `Gamma_n`, `n >= 3`, `g >= 3`, has MF radical `<z^2>` and is not MF.

**Necessary consequences (used as tests).**
- `(OHS1)` forces `lim tr_(d_k) phi_k(z^2) = 1` along every operator-norm model of `Gamma~`, since
  genuine representations kill `z^2` (Malcev and `deligne-covers-of-sp2g-z-have-finite-residual-2z`).
  So the operator-norm twist parameters of `Sp_(2g)(Z)` would all lie in `(1/2)Z/Z`.
- A finite group or a free group satisfies both `[T_2]` and operator-HS-stability, so the
  conjecture is not vacuous on its hypothesis class.

## Attempts

- **Kazhdan projections round the finite-dimensional part in operator norm.** `Gamma~` has (T), so
  each finite-dimensional irreducible `sigma` gives a minimal central projection `p_sigma` in
  `C^*(Gamma~)` with `p_sigma C^*(Gamma~) = M_(dim sigma)`. An operator-norm model induces a
  `*`-homomorphism into the norm corona `prod M_(d_k) / sum M_(d_k)`. The image of `p_sigma` lifts
  to asymptotically central projections `Q_k^sigma`, and matrix algebras are semiprojective, so on
  `Im Q_k^sigma` the model is operator-close to a multiple of `sigma`. For any finite set of
  irreducibles this part rounds, even in operator norm.
  - **Where it dies.** The remainder `1 - sum_(sigma in F) Q_k^sigma` carries a limit trace that
    vanishes on every `p_sigma`: a *diffuse* model. Mass on irreducibles of unbounded dimension is
    allowed, so this is not a contradiction. Nothing on main rounds diffuse models.
- **Diffuse models: the trace does not decide rounding.** After the test above, a diffuse limit trace
  kills `z^2 - 1`. But two operator-norm models with the same limit trace need not be HS-close to
  each other when the group is non-amenable (the embeddings of its von Neumann algebra into `R^omega`
  are not all conjugate). So rounding needs the *model*, not only its trace. Operator-norm models of
  higher-rank lattices are themselves poorly understood: whether they exist beyond finite quotients
  is the open MF question (compare `sl3z-purely-matricial-field`).
- **DGLT correction in operator norm stops after one step.** With operator defect `tau`, `Ad phi_k`
  is an operator-almost representation on `(M_d, HS)`, and `[T_2]` gives a correction `b` with
  `||b||_HS <= K tau`. There is no operator bound on `b`, so after one correction the operator
  defect is uncontrolled and the normalized quadratic remainder is not dimension-free
  (`normalized-hs-taylor-remainder-is-not-dimension-free`).
- **Uniform Schatten vanishing would need growing exponents.** An estimate `||b||_(S_p,norm) <= K_p
  tau` with `K_p` polynomial in `p`, used at `p = log d`, would bound `||b||_op` by
  `K_(log d) tau`. The iteration then contracts only for `tau <~ 1/poly(log d)`: a polylogarithmic
  operator floor, not `(OHS1)`. No such Schatten-coefficient vanishing for `Gamma~` is known here.
