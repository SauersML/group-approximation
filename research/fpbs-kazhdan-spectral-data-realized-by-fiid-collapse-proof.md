---
rg: 2
id: fpbs-kazhdan-spectral-data-realized-by-fiid-collapse-proof
kind: route
title: Split the two-point state into a theta-squared atom plus a reduced state by random finite-cluster signs, then realize every such profile by an FIID collapse family over FIID central spines
target: fpbs-kazhdan-spectral-data-realized-by-fiid-collapse
requires:
  - fpbs-bernoulli-lazy-covariance-bound
  - fpbs-critical-no-infinite-cluster
  - fpbs-soft-collapse-iff-invariant-sparse-spines
  - fpbs-central-z2-groups-have-fiid-sparse-spines
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - fpbs-simple-generating-set-with-gap-exists
---

Notation is as in the target. `Gamma` is infinite, finitely generated and
nonamenable, `S = S^-1` is finite, and `G = Cay(Gamma,S)`. Let
`A = (1/2)(1 + |S|^-1 sum_(s∈S) s)` in `C Gamma`. It is self-adjoint and
positive in every unitary representation. Put `rho = ||lambda(A)||`, which is
`< 1` by Kesten. Let `epsilon` be the trivial character and `C*_r` the reduced
C*-algebra.

## Part I. Structure of two-point states under uniqueness

**Standing hypothesis (H).** `omega` is an invariant bond percolation on `G`
that is a factor of iid. Explicitly, `omega = Phi(Xi)`, where `Xi` is an iid
process indexed by a countable free `Gamma`-set and `Phi` is equivariant and
measurable. Moreover, a.s., either every cluster is finite, or there is exactly
one infinite cluster `I`. Put `theta = P(o ∈ I)`, with `theta = 0` in the first
case, and `phi(x) = P(o <-> x)`.

Every `omega = xi_p` of Bernoulli percolation satisfies (H) whenever it is not
in a nonuniqueness phase. In particular, under collapse `p_c = p_u`, `xi_p`
satisfies (H) for every `p`: there is no infinite cluster for `p <= p_c`, by
`fpbs-critical-no-infinite-cluster` at `p_c`, and uniqueness holds for
`p > p_u`.

`phi` is positive definite. For finitely supported `a`,
`sum_(x,y) a_x conj(a_y) P(x <-> y) = E sum_(clusters C) |sum_(x∈C) a_x|^2 >= 0`,
and `P(x<->y) = phi(x^-1 y)` by invariance. Let `s` be the associated state on
`C*(Gamma)`, so that `s(x) = phi(x)`.

**Theorem I.1 (atom plus reduced).** Under (H) there is a positive functional
`sigma` on `C*(Gamma)` that factors through `C*_r`, with
`sigma(1) = 1 - theta^2`, such that

`s = theta^2 epsilon + sigma`.

*Proof.* Enlarge `Xi` by independent iid labels `beta_x ∈ [0,1]` and
`eps_x ∈ {±1}`, indexed by vertices. For a finite cluster `C` let `m(C)` be its
vertex of minimal `beta`, and put `sigma_C = eps_(m(C))`. Define

* `F(x) = sigma_(C(x))` if the cluster `C(x)` is finite, and `0` otherwise;
* `J(x) = 1[x ∈ I] - theta`.

Both are equivariant measurable functions of the enlarged iid process, and
`E F(o) = 0 = E J(o)`. Put `Z = F + J`. Then:

* `E[F(o)F(x)] = P(o <-> x, C(o) finite)`. If `o` and `x` lie in distinct
  finite clusters, the signs are independent and fair given `(omega,beta)`.
* `E[J(o)J(x)] = P(o,x ∈ I) - theta^2`.
* `E[F(o)J(x)] = E[J(x) E[F(o) | omega,beta]] = 0`, and symmetrically.

By uniqueness, `{o <-> x} = {o <-> x, C(o) finite} ⊔ {o ∈ I, x ∈ I}`. So

`phi(x) = theta^2 + E[Z(o)Z(x)]`.   (I.1)

Let `kappa` be the Koopman representation of the Bernoulli shift on
`L^2_0` of the enlarged iid space. Writing `Z(x) = kappa(x)Z(o)`, (I.1) reads
`phi(x) = theta^2 + <kappa(x)Z(o), Z(o)>`. The representation `kappa` is
contained in a multiple of `lambda`: this is the finite-tensor decomposition
behind `fpbs-bernoulli-lazy-covariance-bound`, in which each chaos summand is
induced from the finite stabilizer of a finite nonempty subset. So
`sigma(a) = <kappa(a)Z(o), Z(o)>` factors through `C*_r`. Finally,
`sigma(1) = E Z(o)^2 = P(C(o) finite) + theta(1-theta) = 1 - theta^2`. ∎

**Corollary I.2 (what the state can see).** Under (H):

1. *Kazhdan projection.* If `Gamma` has (T) and `p_0 ∈ C*(Gamma)` is its
   Kazhdan projection, then `s(p_0) = theta^2`. Indeed `lambda` has no
   invariant vectors, so `lambda(p_0) = 0` and `sigma(p_0) = 0`.
2. *No mass near the trivial representation.* The GNS representation of `s` is
   `theta·1 ⊕ pi_sigma` with `pi_sigma ≺ lambda`. The reduced dual is closed
   in the Fell topology and does not contain `1`, by nonamenability. So some
   Fell neighbourhood of `1` carries no part of `pi_sigma`. This holds for every
   nonamenable `Gamma`, with or without (T).
3. *Gap on the non-trivial part.* For every unit vector `xi` of `pi_sigma`,

   `|S|^-1 sum_s ||pi_sigma(s)xi - xi||^2 = 4 - 4<pi_sigma(A)xi, xi>
   >= 4(1 - rho) > 0`,

   because `pi_sigma ≺ lambda` gives `||pi_sigma(A)|| <= rho`. For a
   representation `pi` put `k_2(pi)^2 = inf_xi |S|^-1 sum_s ||pi(s)xi - xi||^2`
   over unit vectors. Since `lambda(A) >= 0`, the top of its spectrum is
   `||lambda(A)|| = rho`, so `k_2(lambda)^2 = 4(1-rho)` and
   `k_2(pi_sigma) >= k_2(lambda)`. The averaged Kazhdan constant `k_2(Gamma,S)`
   is the infimum of `k_2(pi)` over all representations without invariant
   vectors, a class that contains `lambda`, so `k_2(Gamma,S) <= k_2(lambda)
   <= k_2(pi_sigma)`. Property (T) therefore imposes no constraint on `sigma`
   beyond what Kesten already gives.
4. *Walk sampling.* `a_n := s(A^n) = theta^2 + integral_[0,rho] u^n dnu(u)`,
   where `nu` is the spectral measure of `pi_sigma(A)` at `Z(o)`, of mass
   `1 - theta^2`. This is Theorem 4.1 of `research/artifacts/fpbs/spectral-spike.md`
   (`fpbs-uniqueness-spectral-atom-decomposition`), rederived here for any
   `omega` satisfying (H).
5. *Critical point.* If `theta = 0` then `s = sigma` is reduced. For Bernoulli at
   `p_c` this is also what Hutchcroft's bound `tau_(p_c)(o,x) <= gr^(-|x|/2)`
   gives: it yields `phi ∈ ell^(2+eps)` for every `eps>0`, hence `s` reduced by
   Cowling–Haagerup–Howe. The bound and collapse agree on this point.

**Remark I.3 (the converse direction fails; calibration on trees).** By
Theorem I.1, if some Bernoulli state `s_p` has a non-reduced part beyond the
atom `theta^2 epsilon`, then `xi_p` violates (H), so `p` lies in a
nonuniqueness phase and `p_c < p_u`. The converse fails. On `T_d`, with
`q = d-1`, we have `phi_p(x) = p^|x|` and `p_c = 1/q`, `p_u = 1`. The
spherical function `p^|x|` is tempered exactly for `p <= q^(-1/2)`, so for
`p ∈ (1/q, q^(-1/2)]` the state is reduced inside a true window. The
non-reducedness criterion is therefore sufficient but not necessary for a
window. It says no more than (4.5) of the spectral-spike artifact: it cannot
certify a window from data at `p <= p_c`.

## Part II. An FIID collapse family on class Z

Let `Gamma` be in class `Z` of `fpbs-central-z2-groups-have-fiid-sparse-spines`
and nonamenable. For every `S` that claim gives FIID spines. Run Steps 1–4 of
the proof of Theorem A in `fpbs-soft-collapse-iff-invariant-sparse-spines-proof`
with the following choices:

* the levels `L_k` are FIID spines of density `<= 2^-k`, built from disjoint
  independent iid inputs;
* the connector labels, the tie-breaking labels and the Bernoulli labels `U_e`
  are further independent iid inputs.

This gives `omega_t = xi_t` for `t <= p_c`, and `omega_t = xi_(p_c) ∪ Omega_(n(t))`
for `t > p_c`. Here `Omega_n = ∪_(k>=n)(L_k ∪ C_k)` and `n(t) = ceil(1/(t-p_c))`.

**Proposition II.1.** Jointly in `t`, `(omega_t)` is an equivariant measurable
function of one iid process. It satisfies (S1)–(S4). For `t > p_c` it has a
unique infinite cluster, and `theta(t) -> 0` as `t ↓ p_c`. Every `omega_t`
satisfies (H). Moreover `phi_t -> phi_(p_c)` pointwise as `t ↓ p_c`, so
`s_t -> s_(p_c)` weak-*.

*Proof.*

* *Factor of iid.* Each `L_k` and `C_k` is an equivariant measurable function
  of its own inputs. `Omega_n` is a countable union and is a.s. locally finite
  in the index `k`, by Step 3 (Borel–Cantelli), so it is measurable. The
  properties (S1), (S2), insertion tolerance and (S4) are proved in Theorem A
  from connectivity of the levels, existence of connectors and critical
  finiteness. These hold here without change.
* *Ergodicity.* A factor of a Bernoulli shift is mixing, so no ergodic
  decomposition is needed.
* *(H).* It holds for `t <= p_c` by `fpbs-critical-no-infinite-cluster`, and
  for `t > p_c` by (S4).
* *Continuity.* `P(o <-> x in omega_t) - P(o <-> x in xi_(p_c))` is at most
  `P(C_xi(o) ∩ V(Omega_(n(t))) ≠ ∅)`, where `C_xi(o)` is the cluster of `o` in
  `xi_(p_c)`. This tends to `0` by the dominated-convergence step of Theorem A,
  (S4). Monotonicity gives the lower bound `>= 0`. Pointwise convergence of
  normalized positive definite functions is weak-* convergence of the states,
  because `Gamma` spans a dense subspace of `C*(Gamma)` and the states are
  uniformly bounded. ∎

**Consequently** the family realizes the whole collapse profile of
Corollary I.2 for every `t`:

* `s_t = theta(t)^2 epsilon + sigma_t` with `sigma_t` reduced;
* `s_t(p_0) = theta(t)^2 -> 0`;
* the Kesten gap on the non-atomic part;
* the walk-sampling moments `a_n(t) = theta(t)^2 + integral_[0,rho] u^n dnu_t`;
* `s_(p_c)` equal to the critical Bernoulli state, including Hutchcroft's
  bound, `ell^(2+eps)` summability and reducedness;
* weak-* continuity at `p_c`;
* `p_u = p_c` for the family.

## Corollary (class-killing obstruction)

Let `Gamma~_n = p^-1(Sp_2n(Z))` for `n >= 2`. It has property (T) and lies in
class `Z` (`fpbs-central-z2-groups-have-fiid-sparse-spines`, Examples). It is
nonamenable. Fix any finite symmetric generating set `S`.

Suppose an argument claims to prove `p_c(G) < p_u(G)` on `G = Cay(Gamma~_n,S)`
by deriving a contradiction from `p_u = p_c`, and uses only:

1. facts about Bernoulli percolation at `p <= p_c` (sharpness, tail bounds,
   critical no-percolation, Hutchcroft's critical bound);
2. the soft properties of the supercritical family: (S1)–(S4), uniqueness,
   factor-of-iid, mixing, continuity of `theta`;
3. the spectral data of the two-point states `s_t`: the Kazhdan projection
   values, Fell-support in `{1} ∪ Gamma^_r`, Kazhdan and Kesten gaps of the
   non-trivial part, the walk-sampling moments and measures, weak-* continuity
   at `p_c`, and everything derived from items 1–3 through the GNS construction.

Then the same argument applies to the family of Part II on `G`, whose inputs of
all three kinds are satisfied, and it concludes `p_c < p_u` for a family that
has `p_u = p_c`. So no such argument exists. By
`fpbs-simple-generating-set-with-gap-exists`, some `S` makes Bernoulli
percolation on `Cay(Gamma~_n,S)` have a true window. On that graph both the true
window and the FIID collapse satisfy every constraint in items 1–3.

## Exact failing steps of the spectral-gap mechanism

* **(F1) "The mass near `1` but not on it carries the transition."** Under
  collapse there is no such mass for any `t` (Corollary I.2.2). The non-atomic
  part is reduced, and it is separated from `1` by the Kesten gap. That gap
  holds for every nonamenable group, so property (T) adds nothing. The only
  piece that moves at `p_c` is the atom `theta(t)^2`. It is continuous, and
  the Kazhdan projection is exactly the functional `s -> theta^2` that the
  sw-029 attempt on the target already found silent.
* **(F2) Hutchcroft's bound versus collapse.** They are compatible. The bound
  forces `s_(p_c)` to be reduced (Corollary I.2.5), which is exactly the
  `theta = 0` case of the collapse profile. The FIID family realizes both.
* **(F3) Where a contradiction must come from.** The exponential pivotal-spike
  theorem (`fpbs-collapse-exponential-pivotal-spikes`) turns growth of `a_n`
  into conditional pivotal counts. It does this through Russo's identity (6.1)
  and the product structure of `xi_t` above `p_c`, and the family has neither.
  In the family, the increase from `p_c` to `p_c + eps` adds a whole connected
  spine at once, and `omega_t` for `t > p_c` is not a product measure, so the
  finite-volume Russo identity is unavailable. So any successful proof
  must use a quantitative consequence of independent increments above `p_c`,
  such as Russo, BK or submultiplicativity, and not the representation theory
  of `tau_t`.
* **Not claimed.** Deletion tolerance and Harris–FKG are not decided for this
  family. The family of
  `fpbs-finite-energy-fkg-collapse-over-central-z2-slabs` has both of those
  properties but is not FIID. No known family on a Kazhdan graph has FIID,
  deletion tolerance and FKG simultaneously.
