---
rg: 2
id: abelianized-cover-injective-corona-model-carries-nonzero-twist
kind: claim
title: A corona model of the abelianized cover of a full-MF-radical group with zero pushed relation-module class kills the commutator with the kernel
distinct_from:
  free-abelianized-cover-reflects-mf: that is the open descent statement; this proves one necessary condition on any injective corona model of the cover of a full-radical base and does not decide descent.
  free-abelianized-cover-fd-radical-is-commutator: that kills the whole commutator subgroup in exact finite-dimensional representations; this works in operator-norm coronas and kills only [E,M], and only for models whose pushed class vanishes.
  bernoulli-maximizes-extension-class-norm: that measures an extension class in measurable cohomology of probability-preserving actions; this pushes the relation-module class into the unitary group of a commutative corona subalgebra and uses the full MF radical of the quotient to force a splitting to be trivial.
  isr-actors-force-holonomy-into-an-abelian-kernel: that concerns invariant-subalgebra-rigid actors; this uses no rigidity of the action, and by implemented-corona-actions-of-countable-groups-are-unconstrained no such rigidity is available.
---

**ESTABLISHED.**

## Setting

- `F` is free, `R` is normal in `F`, and `G = F/R` has `Rad_MF(G) = G`.
- `E = F/[R,R]`, `M = R/[R,R]`, and `xi in H^2(G; M)` is the class of
  `1 -> M -> E -> G -> 1`.
- `Q = prod M_(k_n) / (+) M_(k_n)` is any norm matrix corona, and
  `rho : E -> U(Q)` is any homomorphism.
- `B = C*(rho(M))` is a unital commutative C*-subalgebra, `B = C(X)`.

## Statement

1. **Action.**  `rho(E)` normalizes `B`, and `M` acts trivially on it.  So `G`
   acts on `B` by `g . b = rho(gt) b rho(gt)^*`, where `gt` is any lift of `g`.
   The group `U(B) = C(X,T)` is a `G`-module, and `rho|_M : M -> U(B)` is
   `G`-equivariant.  Let `rho_* xi in H^2(G; U(B))` be the pushed class.
2. **Dichotomy.**  If `rho_* xi = 0`, then `rho(gt) in U(B)` for every `g`, the
   action is trivial, and `rho([E,M]) = 1`.
3. **Consequence.**  Suppose moreover `G != 1`, so that `[E,M] != 1` (see
   `full-mf-radical-abelianized-cover-is-not-mf`).  Then every injective `rho`
   has a nontrivial action of `G` on `X` and `rho_* xi != 0`.
4. **Scope of the coefficients.**  Let `A = rho(M)' cap Q` be the relative
   commutant.  In it `rho(M)` is central, and it is `rho(E)`-invariant.  The
   nonabelian pushout with coefficients `U(A)` splits **if and only if**
   `rho([E,M]) = 1`.  So that version is only a restatement.  The abelian
   criterion in item 2 is a genuine sufficient condition, and it is strictly
   one-directional: zero class forces `rho([E,M]) = 1`, and nothing is claimed
   in the other direction.

## Proof

**Item 1.**  Conjugation by `rho(e)` maps `rho(M)` onto itself because `M` is
normal.  Elements of `rho(M)` commute with `B`, because `B` is commutative.
So the conjugation action factors through `G`, and equivariance is
`rho(e m e^-1) = rho(e) rho(m) rho(e)^*`.

**Item 2, the pushout.**
- Form `U(B) x| E`, with `E` acting through `rho`-conjugation, and multiplication
  `(b,e)(b',e') = (b (e . b'), e e')`.
- The antidiagonal `N = {(rho(m)^-1, m) : m in M}` is a subgroup because
  `U(B)` is abelian and `rho|_M` is equivariant.  It is normal:
  `(b,e)(rho(m)^-1, m)(b,e)^-1 = (rho(e m e^-1)^-1, e m e^-1)`.  To see this,
  note that `b` commutes with `rho(m)`, and `m` acts trivially on `B`.
- `E' = (U(B) x| E)/N` is an extension `1 -> U(B) -> E' -> G -> 1` whose class
  is `rho_* xi`.  This is the standard pushout description of the change of
  coefficients `H^2(G; M) -> H^2(G; U(B))`.
- The map `Psi(b,e) = b rho(e)` is a homomorphism to `U(Q)`, because
  `b rho(e) b' rho(e') = b (rho(e) b' rho(e)^*) rho(e e')`.  It kills `N`.

**Item 2, the splitting.**
- If `rho_* xi = 0`, choose a homomorphic section `sigma : G -> E'`, and write
  `sigma(g) = [(b_g, gt)]`.
- Then `s = Psi o sigma : G -> U(Q)` is a homomorphism, so
  `s(g) = b_g rho(gt) = 1` for all `g`, because `Rad_MF(G) = G`.
- Hence `rho(gt) = b_g^* in U(B)`.  So `rho(gt)` commutes with `rho(M)`, and
  `rho([gt, m]) = 1`.

**Item 3.**
- **`[E,M] != 1`.**  `G` is infinite, because finite groups are MF and
  `G != 1`.  The Lyndon relation sequence `0 -> M -> ZG^n -> I_G -> 0` makes
  `M` a submodule of `ZG^n`.  For infinite `G`, `(ZG^n)^G = 0`, so `M^G = 0`.
  If `M = 0`, then `R = [R,R]`; a free group equal to its commutator subgroup
  is trivial, so `G = F` would be free, hence residually finite and MF, a
  contradiction.  So `M` is a nonzero module with no fixed points, and
  `[E,M]`, the image of `I_G M`, is nontrivial.
- An injective `rho` does not kill `[E,M] != 1`.  By item 2 its
class is nonzero.  If its action were trivial, every `rho(gt)` would commute
with `rho(M)`, and `rho` would kill `[E,M]`; so the action is nontrivial.

**Item 4.**  The pushout with `U(A)` is formed the same way.  Normality of the
antidiagonal uses only that `rho(M)` is central in `A`.
- If it splits, the argument of item 2 gives `rho(gt) in U(A)`, that is,
  `rho([E,M]) = 1`.
- Conversely, if `rho([E,M]) = 1`, then `rho(E) <= U(A)`, and
  `g -> [(rho(gt)^-1, gt)]` is a well-defined homomorphic section.  Changing
  the lift `gt` to `gt m` multiplies by an element of `N`, because `rho(gt)`
  commutes with `rho(m)`.

## Where this stops

- The class `rho_* xi` lives in `H^2(G; C(X,T))` for an action of `G` on the
  spectrum `X`.
- On a fixed point `x` of the action, evaluation gives a class in
  `H^2(G; T)`.  A full-radical group has no proper finite-index subgroup,
  because finite groups are MF, so every finite orbit is a fixed point.
  Nontrivial actions have infinite orbits.
- A proof of `(DF)` would have to show that the class vanishes for every
  model, or that `rho([E,M]) = 1` for some other reason.
- `implemented-corona-actions-of-countable-groups-are-unconstrained` shows
  that the action alone cannot supply either conclusion.
