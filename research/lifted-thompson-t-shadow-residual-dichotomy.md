---
rg: 2
id: lifted-thompson-t-shadow-residual-dichotomy
kind: claim
title: "The operator-to-HS shadow residual of T-bar is trivial or everything; so MF T makes T-bar hyperlinear, any gapped commutant corner of the centre makes T-bar hyperlinear, and on the other branch every corona representation of T-bar is trace-null with connected central spectrum"
distinct_from:
  lifted-thompson-t-mf-radical-dichotomy: that is the same all-or-nothing dichotomy for the MF radical Rad(T̄); this one is for the shadow residual S(T̄) = R_(infinity->2)(T̄), which contains Rad(T̄) and can be strictly larger. Its trivial branch gives hyperlinearity of T̄, not MF-ness, and it holds whenever T is MF.
  central-eigencorners-die-over-full-radical-quotients: that needs an exact scalar eigencorner and full radical of T; this needs only a commutant corner on which rho(z) - 1 is invertible, and concludes hyperlinearity of T̄ instead of a contradiction.
  thom-central-corner-criterion: that descends hyperlinearity from a group to a central quotient; this goes up, from MF-ness of T (or one gapped corner) to hyperlinearity of the central extension T̄.
  hs-invisible-corona-maps-are-full-trace-paddings: that describes the corona maps of any group with full shadow residual; this proves the full-or-trivial dichotomy for T̄ and adds that on the full branch every commutant corner of every corona map has connected central spectrum through 1.
  gapped-normal-generators-give-a-hyperlinear-quotient: that needs a spectral gap at 1 for a normal generator; z is not a normal generator of T̄, and this uses an invertibility gap of rho(z) - 1 on a commutant corner instead.
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`lifted-thompson-t-shadow-residual-dichotomy-proof`.

Notation as in `lifted-thompson-t-mf-radical-dichotomy`: `T̄` is the lift of
Thompson's `T` to `R`, `z(x) = x + 1` is its central translation and
`p : T̄ -> T` has kernel `<z>`.  `Q` is a norm matrix corona
`prod_n M_(k_n) / (+)_n M_(k_n)`.  `S(G) = R_(infinity->2)(G)` is the
operator-to-HS shadow residual of `op-to-hs-shadow-residual-functoriality`:
the elements `g` with `||U_n(g) - 1||_(2,tr) -> 0` along every free
ultrafilter, for every operator-norm asymptotic representation `U_n` of `G`.
Equivalently, for every corona homomorphism `rho` and unitary lifts
`U_n(g)` of `rho(g)`.

For a corona homomorphism `rho : T̄ -> U(Q)`, a *gapped commutant corner* is a
nonzero projection `P in rho(T̄)' ∩ Q` such that `rho(z) P - P` is invertible
in `P Q P`.

1. **(Dichotomy.)**  `S(T̄) in {1, T̄}`.  So `z in S(T̄)` iff `S(T̄) = T̄` iff
   `S(T̄) != 1`.
2. **(Trivial branch.)**  If `S(T̄) = 1`, then `T̄` is hyperlinear, and so is
   `T`.  This branch holds in each of the following cases:
   - (a) `T` is MF.  So **if `T` is MF, then `T̄` is hyperlinear.**
   - (b) Some corona homomorphism of `T̄` has a gapped commutant corner.
   - (c) Some corona homomorphism `rho` of `T̄` has, for some nonzero
     projection `q in rho(T̄)' ∩ Q` and some `lambda`, `||(rho(z) - lambda) q|| < |lambda - 1|`.
     This includes an exact eigencorner `rho(z) q = lambda q` with `lambda != 1`.
3. **(Full branch.)**  If `S(T̄) = T̄`, then:
   - `T` has full MF radical (`T` is not MF);
   - every corona homomorphism of `T̄` is a full-trace padding of a
     trace-null remainder, as in `hs-invisible-corona-maps-are-full-trace-paddings`;
   - for every nonzero `P in rho(T̄)' ∩ Q`, the corner representation
     `rho_P = rho(.) P` on `PQP ≅ prod M_(r_n) / (+) M_(r_n)` satisfies
     `tau_omega(rho_P(g)) = 1` for every `g` and every ultralimit trace
     `tau_omega` of that corona;
   - for every corona homomorphism `rho` of `T̄`, every `k >= 0` and every
     nonzero projection `P` commuting with `rho(lambda^k(T̄))`, the spectrum
     of `rho(t_k) P` in `P Q P` is **connected and contains 1**.  Here
     `lambda(g)(x) = g(2x)/2` is the dilation and `t_k = lambda^k(z)` is
     translation by `2^(-k)`.  For `k = 0` this is `rho(z) P`, for every
     nonzero `P in rho(T̄)' ∩ Q`.
4. **(Where the branches sit.)**
   ```text
   T̄ not hyperlinear  ==>  S(T̄) = T̄  ==>  T not MF
   T̄ not MF (lifted-thompson-t-is-not-mf)  ==>  S(T̄) = T̄
   ```

## What this changes

- **`T` MF gives the central extension for free, tracially.**  Item 2(a) is
  new two-way information.  `lifted-thompson-t-mf-radical-dichotomy` gives
  "`T` MF implies `T̄` MF".  This gives "`T` MF implies `T̄` hyperlinear".
  So a refutation of the flagship hole by an MF model of `T` also makes
  every Euler-twisted algebra `L_(s·eu)(T)` (`s in R/Z`) Connes embeddable,
  by Thom's Lemma 3.3 in `thom-central-corner-criterion`.  No
  `mf-implies-hyperlinear` input is used: the torsion normal generators of
  `T` supply the gap for `T`, and the dilation carries it to `T̄`.
- **Exact eigencorners are more than the flagship needs.**  Item 2(b)-(c)
  says one gapped commutant corner already puts `T̄` on the trivial branch.
  This gives the second exact decomposition
  `lifted-thompson-t-not-mf-via-gapped-corners`:
  ```text
  lifted-thompson-t-is-not-mf  <=>  lifted-thompson-t-shadow-residual-is-full
                                     AND lifted-thompson-t-centre-has-gapped-commutant-corners
  ```
  It trades the exact scalar corner of
  `lifted-thompson-t-not-mf-via-central-eigencorners` for an invertibility
  gap. The price is that "`T` not MF" is strengthened to the tracial
  statement `S(T̄) = T̄`.
- **Precise obstruction for tracial approaches (entropy, measure,
  character).**  On the full branch, let `P` be any nonzero commutant
  corner of any corona homomorphism `rho` of `T̄`.  Then the corner
  representation `rho_P` is HS-invisible in the renormalized ultralimit
  traces of `PQP`: `tau_omega(rho_P(g)) = 1` for every `g` and every
  `omega`.  Its central spectrum there is a connected arc through `1`.  So
  no ultralimit trace of any commutant corner distinguishes a
  counterexample `rho` from the trivial representation.  This is the configuration of
  `o2-suspension-central-unitary-evades-commutant-corners`.  A tracial
  argument can prove at most `S(T̄) = T̄`.  The remaining conjunct is
  norm-only, and it dies exactly where general extraction died.
