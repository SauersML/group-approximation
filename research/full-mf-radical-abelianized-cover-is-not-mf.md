---
rg: 2
id: full-mf-radical-abelianized-cover-is-not-mf
kind: claim
title: The free abelianized cover of a nontrivial full-MF-radical group is not MF
distinct_from:
  free-abelianized-cover-reflects-mf: that is descent (D) for every presentation of every group; this is only its contrapositive for bases with FULL MF radical, where every corona homomorphism of the base is trivial and not merely non-injective.
  free-abelianized-cover-fd-radical-is-commutator: that computes the exact finite-dimensional radical of the same cover, a larger radical whose total collapse is compatible with MF; this asks for the operator-norm corona radical.
  abelianized-cover-commutator-is-finitely-generated-perfect: that is group theory of the commutator core; this is the analytic non-MF statement.
artifacts:
  - research/abelianized-cover-injective-corona-model-carries-nonzero-twist.md
  - research/implemented-corona-actions-of-countable-groups-are-unconstrained.md
  - research/dummy-abelianized-cover-df-splits-regular-trace-and-shadow.md
  - research/relation-lamp-wreath-is-mf-with-nontrivial-fd-radical.md
  - research/stable-abelianized-cover-is-subgroup-monotone.md
---

**OPEN.**  Let `F` be free of finite rank, `R` normal in `F`, and suppose
`G = F/R != 1` has `Rad_MF(G) = G`.  Set `E = F/[R,R]` and `M = R/[R,R]`.
The claim is that `E` is not MF:

```text
every homomorphism rho : E -> U(prod M_(k_n) / (+) M_(k_n)) has nontrivial kernel.   (DF)
```

The route `property-t-free-seed-via-leavitt-abelianized-cover` uses only one
instance: the finite presentation that
`full-mf-radical-has-fp-cover-same-generators` gives over
`St_20(L_(F_2)(1,2))`.

`free-abelianized-cover-reflects-mf` implies `(DF)`.  The converse is not
claimed.

**Known structure.**

- A nontrivial full-MF-radical group is infinite, because finite groups are MF.
- For infinite `G`, the relation module `M` is a nontrivial `G`-module with no
  fixed vectors.  It embeds in `ZG^n` by the Lyndon sequence, and
  `(ZG^n)^G = 0`.  Moreover `M != 0`, since otherwise `R` is perfect, hence
  trivial, and then `G` is free, hence MF.
- So `[E,M]`, which is the image of `I_G M`, is a nontrivial normal subgroup
  of `E`.

## Attempts

- **Untwisting dichotomy (2026-09-18).**
  `abelianized-cover-injective-corona-model-carries-nonzero-twist` proves:
  - if a model `rho` has zero pushed class
    `rho_* xi in H^2(G; U(C*(rho(M))))`, then `rho` kills `[E,M] != 1`;
  - so an injective model of `E` must act nontrivially on the spectrum of
    `C*(rho(M))`, and it must carry a nonzero abelian twist class there.

  This does not close `(DF)`.  Nothing shows that a nonzero class cannot occur,
  and the nonabelian-coefficient form of the dichotomy is a tautological
  restatement of `rho([E,M]) = 1`.
- **Rigidity of the induced action is false as a principle (2026-09-18).**
  `implemented-corona-actions-of-countable-groups-are-unconstrained` realizes
  every nontrivial countable group, full MF radical or not, by a nontrivial
  action on a commutative subalgebra `C(X)` of a matrix corona.  The action is
  implemented by unitaries whose cocycle lies in the relative commutant.
  - Any proof of `(DF)` must therefore use the finer data of an actual model:
    the cocycle takes values in `U(C*(rho(M)))` itself, and it is the image of
    the relation module.
  - A counterexample must realize such a cocycle exactly with commuting
    conjugates.  The Bernoulli construction does not: its permutation
    holonomy lies only in the commutant.
- **Regular-trace / shadow split for the dummy presentation (2026-09-18).**
  `dummy-abelianized-cover-df-splits-regular-trace-and-shadow` proves the
  following for the dummy cover `E_z`, where `C(M_z) = M_z`.
  - Every nontrivial normal subgroup of `E_z` meets `M_z`.
  - `delta_e` is an operator-norm MF character of `E_z` iff the shadow
    residual `S(E_z)` is trivial, iff every nonzero `m in M_z` has some
    operator-norm MF character with `tau(m) != 1`.  The proof averages the
    witnesses, Diracizes the average, and uses the self-centralizing kernel
    to force the scalar kernel to be trivial.
  - So DF for `E_z` is equivalent to `(REG)` and `(SH)`:
    - `(REG)`: no operator-norm microstates of `delta_e`.  These would come
      with `C(hat M_z)` at Haar trace, full spectrum, and a mixing,
      essentially free dual action.
    - `(SH)`: `S(E_z) != 1` implies `Rad_MF(E_z) != 1`.
  - DF for `E` implies DF for `E_z`, because `E` is a retract of `E_z`.

  **Where it dies.**
  - The attempt to get more than this from a surviving `[E,M]` element fails
    at the renormalized trace `tr(y_n)/tr(a_n)`.  When `tr(a_n) -> 0` it is
    not a corona invariant: lift changes and operator-norm defects are
    `o(1)`, not `o(tr a_n)`.  So tracially blind models such as
    `rho (+) 1_(N_n)` cannot be handled by trace renormalization.
  - Handling those models is exactly `(SH)`.
  - `mf-vs-tracial-radical-strict-gap` shows `(SH)` is not formal for
    abelian-by-`G` lamp extensions.
  - Neither `(REG)` nor `(SH)` is proved.
- **Dummy lamp calibration: every argument that ignores `[R,R] = 1` dies at an
  MF group (2026-09-18).**
  `relation-lamp-wreath-is-mf-with-nontrivial-fd-radical` works with the
  dummy presentation `<X, z | R, z>`.
  - Its cover is `E' = ZG x| E`.  It contains `E`, it is torsion free, and it
    suffices for the route.
  - `E'` is the quotient `W/[R,R]` of the lamp group `W = ZG x| F`.
  - `W` is MF, using Hall-separable windows `H_L = <R cap S_L>` and the
    permutation models on `F/K_L`.
  - Yet every nonzero element of `I_G ZG`, for example `[w,z]` with
    `w notin R`, lies in the finite-dimensional radical of `W`, over every
    field.  In the models, `||[w,z] - 1|| = 2`.

  So any proof of `(DF)` for `E'` has to use `rho([r,r']) = 1` among the
  relator images.  Their exact commutation with the lamps, the module
  structure, the finite-dimensional radical and the absence of finite
  quotients of `G` all hold in the MF group `W` and cannot suffice.

  Side results for this lane, not written as separate nodes:
  - **Linear images are abelian.**  Every image of `E` or `E'` in `GL_d(K)`,
    over any field, is abelian.  Its finite quotients are abelian, because
    `G` has none, and Malcev applies.
  - **Exact permutation models reduce to finite quotients.**  An exact
    permutation (LEF-type) corona model of `E` amounts, once the windows are
    reindexed, to a sequence of finite quotients `P_L` of `Gamma_L = F/<<[r,r'] : r,r' in R cap S_L>>`.
    For a finitely presented `G`, `P_L` is the normal closure of the images of
    the defining relators.
  - **Diameter lemma.**  If `L >= 2 diam(P_L) + max|r_j|`, then `P_L` is
    generated by images of `R cap S_L`, which pairwise commute, so `P_L` is
    abelian and the model kills `[E,E]`.  A surviving exact permutation model
    therefore needs `diam(P_L) >= (L - max|r_j|)/2`.

  Open need: finite quotients of `Gamma_L` with `diam(P_L)` growing linearly
  in `L`, in which `[w, r_1]` survives, or a proof that none exist.  For the
  St_20 presentation that would decide `(DF)` within exact permutation models.
- **Presentation-free reduction and subgroup monotonicity (2026-09-18).**
  `stable-abelianized-cover-is-subgroup-monotone` (ESTABLISHED, pure group
  theory) proves the following.
  - `E_(G,X,k) = ZG^k x| E_(G,X)`.
  - Tietze invariance: `E_(G,X,|Y|) = E_(G,Y,|X|)`.  So "stably DF", meaning
    some dummy cover is not MF, does not depend on the presentation.
  - For a finitely generated `H <= G` of infinite index, `P^(-1)(H)` is `H`
    plus `aleph_0` dummies after a basis slide.  So every dummy cover of `H`
    embeds in `E_(G,X)` for EVERY `X`.
  - Stable DF is a commensurability invariant.
  - `E` splits over `H <= G` iff `H` is free.  This uses the Fox projection
    and Stallings--Swan.
  - Amenable and free `H` are never stably DF.

  What the route uses from `(DF)` is exactly "the finitely presented cover
  `G~` of `St_20(L)` is stably DF".  That now follows from stable DF of any
  one finitely generated subgroup of `G~`, of any index, which need not have
  full radical.  If the index is infinite, it gives `(DF)` for every
  presentation with no dummies.

  **Dead as a class.**  Approaches that lift a non-MF subgroup of `G` into
  `E` die at Step 5: nothing non-free lifts.

  **Remaining gap between the invariant and a fixed presentation.**  Can one
  dummy lamp destroy MF?  That is, is `ZG x| E` non-MF while `E` is MF?

  **Not done.**  Stable DF is not proved for any group.  The contrapositive
  says a DF counterexample at `G` makes the stable cover of every finitely
  generated infinite-index subgroup of `G` MF.
