---
rg: 2
id: deligne-lattice-hyperlinear-iff-full-hs-parameter-circle
kind: claim
title: Deligne's universal-cover lattice is hyperlinear iff the HS Maslov parameter group is the whole circle, because the tracial spectrum of the central unitary lies in the HS parameter group
distinct_from:
  deligne-lattice-non-mf-forces-finite-parameter-group: that is the operator-norm statement, whose converse is only conditional on the corner-extraction instance (CPE*); this is the tracial statement, where spectral projections of the central unitary always exist, so the converse and the radical dichotomy are unconditional, and it adds the tracial-visibility constraint on every corona model.
  deligne-hs-parameter-trace-threshold: that defines P_2 and proves (T1)-(T5), with the mod-three reading only at q = 3; this proves the parameter-free equivalence for the lattice E_infinity itself and the reading for every finite cover E_q.
  dogon-sp2g-weak-ucp-nonhyperlinear: that derives non-hyperlinearity of the same lattice from weak ucp-stability of the base; this proves no stability, and identifies the target of that theorem with finiteness of P_2.
  deligne-sector-gap-is-exactly-nonhyperlinearity: that concerns E_3 and one parameter; this concerns E_infinity and the whole parameter group.
  o2-suspension-central-unitary-evades-commutant-corners: that shows central unitaries of a C*-corona can evade every corner trace; this shows that in the tracial ultraproduct they cannot, and names that evasion as the only way to refute the lattice non-MF claim without making the lattice hyperlinear.
---

**ESTABLISHED** through `deligne-lattice-hyperlinear-iff-full-hs-parameter-circle-proof`. Unreviewed; no novelty
claimed for the standard ultraproduct facts used.

**Setting.**
- `Gamma = Sp_4(Z)`. `Gamma~ = E_infinity` is Deligne's lattice with central generator `z`, and `E_q = Gamma~/<z^q>`.
- `b`, `c_theta = exp(2 pi i theta b)` and `P_2` are as in `deligne-hs-parameter-trace-threshold`. By (T1), `P_2` is
  either `R/Z` or `(1/m_2)Z/Z` for one even `m_2`.
- `M = prod_omega M_(k_n)` is a tracial ultraproduct of matrix algebras with trace `tau`. A group is *hyperlinear*
  if it embeds into `U(M)` for some such `M`.
- `e(s) = exp(2 pi i s)`.

**Theorem.**
1. **(H1) Tracial spectral support.** Let `V : Gamma~ -> U(M)` be any homomorphism, `u = V(z)`, and `mu` the
   distribution of `u` under `tau`. Then every point of `supp(mu)` is `e(s)` for some `s` in `P_2`.
2. **(H2) Parameter-free criterion.** `Gamma~` is hyperlinear iff `P_2 = R/Z`. Equivalently, `Gamma~` is not
   hyperlinear iff `P_2` is finite.
3. **(H3) Hyperlinear radical and all covers.** If `P_2 = (1/m_2)Z/Z`, every homomorphism `Gamma~ -> U(M)` kills
   `z^(m_2)`, and `E_(m_2)` is hyperlinear. So the intersection of the kernels of all such homomorphisms is exactly
   `<z^(m_2)>`, with no unconditional hypothesis. For every `q >= 1`,
   ```text
   E_q is hyperlinear   <=>   1/q in P_2 .
   ```
   At `q = 3` this recovers (T5).
4. **(H4) Tracial visibility in coronas.** Let `Theta : Gamma~ -> U(Q)` be a homomorphism into
   `Q = prod_n M_(d_n) / direct_sum_n M_(d_n)`, and let `(u_n)` be unitary lifts of `Theta(z)`. For every free
   ultrafilter `omega`, the `omega`-limit distribution of `u_n` is supported in `sp(Theta(z)) cap e(P_2)`. If `P_2`
   is finite, then `||u_n^(m_2) - 1||_2 -> 0` along the whole sequence.
5. **(H5) Split of the lattice non-MF claim.** `deligne-universal-cover-lattice-is-not-mf` follows from two
   prerequisites, each of which could fail on its own:
   - (HL) `Gamma~` is not hyperlinear, i.e. `P_2` is finite;
   - (IR) *invisible rigidity at `m_2`*: every corona model of `Gamma~` with `||Theta_n(z)^(m_2) - 1||_2 -> 0`
     has `Theta(z)^(m_2) = 1` in `Q`.

**Class killed.** Every refutation of `deligne-universal-cover-lattice-is-not-mf` that is *tracially visible* also
proves that `Gamma~` is hyperlinear, so it also refutes the target of `dogon-sp2g-weak-ucp-nonhyperlinear`. Here
*tracially visible* means an MF embedding `Theta` such that, for every `N >= 1`, some limit trace gives
`Theta(z)^N - 1` a nonzero `||.||_2`. Examples are direct sums of HS-faithful models glued to residually finite data, and every model
with a limit trace faithful on `C*(Theta(z))`.
- *Invariant.* The limit-trace distribution of `Theta(z)`.
- *Step where every member dies.* A spectral projection `1_I(u)` of a short arc `I`, taken in the tracial ultraproduct,
  is a central corner on which `u` is within `|I|` of a scalar in operator norm. That corner is an HS model at a
  parameter within `|I|` of the arc's centre (H1).

What survives is exactly the configuration of `o2-suspension-central-unitary-evades-commutant-corners`: a
separating arc of `sp(Theta(z))` that carries no mass for any limit trace.

**Flagship reading.** `1/3 in P_op` implies `1/3 in P_2`. The HS flagship splits as
```text
E_3 not hyperlinear   <=>   (HL)  and  3 does not divide m_2 .
```
Given (H2), this is (T5) with its first condition renamed as non-hyperlinearity of the lattice. It is the tracial copy
of route `deligne-triple-cover-via-deligne-lattice-non-mf`, with its (CPE*) gap closed.
