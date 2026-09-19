---
rg: 2
id: leavitt-cone-head-bound-is-finite-congruence-gluing
kind: claim
title: The Leavitt cone head bound (QC) is a gluing problem for finite Steinberg groups over finite quotients of the Cuntz cones, and the negative-root relator kappa alone never forces the head
distinct_from:
  leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding: that splits non-hyperlinearity of Delta into (QC) and (HR); this shows every representation entering (QC) has finite, congruence images on both halves, turns (QC) into a statement about finite groups St_20(B) glued over SL_20(F_2)^2, and exhibits an exact finite model killing kappa with the head at distance sqrt 2.
  leavitt-cone-cover-kernel-is-dense-in-every-compact-model: that shows a finite-dimensional representation of Gamma killing all k_i is trivial, and that only asymptotic models survive; this describes those surviving models (both halves act through finite congruence groups, and the head depends only on the edge restriction) and shows that exactly killing kappa is compatible with a far head.
  leavitt-cuntz-cone-halves-have-rf-amalgam-cover: that names kappa as the first K-relator a certificate must use; this shows kappa, and every relator in the kernel of one explicit Cohn-type shadow, is insufficient even exactly.
  leavitt-corner-bcs-support-coefficient-gate: that filters coefficient subrings of R, which contain the isometry relations t_i s_i = 1; this uses finite-dimensional representations of the two cone rings, which do not.
  positive-characteristic-steinberg-unitary-images-are-finite: that is the general finiteness lemma; this is its application to the cone cover of the Leavitt host.
artifacts:
  - research/leavitt-cone-head-bound-finite-congruence-gluing-proof.md
  - research/positive-characteristic-steinberg-unitary-images-are-finite.md
---

**ESTABLISHED** (route `leavitt-cone-head-bound-finite-congruence-gluing-proof`; lane swarm-0917-w17-w17-nh-pull;
unreviewed).

**Setting** (`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`).
- `R = L_(F_2)(1,2)`, `q = s_1 t_1`, `Delta = St_20(R) = GL_20(R)`, `z = x_13(q)`.
- `R_+ = <s_1, s_2, q>`, `R_- = <t_1, t_2, q>`, `R_0 = R_+ ∩ R_- = F_2 + F_2 q`.
- `Delta_+- = E_20(R_+-)`, `Delta_0 = SL_20(F_2)^2`, `Gamma = Delta_+ *_(Delta_0) Delta_-`.
- `K = ker(Gamma -> Delta)` is the normal closure of `k_1, ..., k_r`, and
  `kappa = [x_12(s_1), x_23(t_1)] z^(-1) ∈ K`.
- `(QC)` is as in `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`. Norms are normalized
  Hilbert–Schmidt.

**Theorem.**
1. **Congruence reduction.** For every unitary `rho : Gamma -> U(d)`:
   - there are two-sided ideals `I_+- ⊆ R_+-` of index at most `2^d` such that `rho|Delta_+-` kills every
     `x_ij(I_+-)`;
   - `rho(Delta_+-)` is a finite quotient of `St_20(R_+-/I_+-)`, of order at most `|E_20(R_+-/I_+-)| · d^d`;
   - `rho` factors through the virtually free amalgam `rho(Delta_+) *_(rho(Delta_0)) rho(Delta_-)` of finite groups.
2. **Elementary congruence property of the halves.** Every finite-index normal subgroup of `Delta_+-` contains a
   relative elementary subgroup `E_20(R_+-, J)` for some two-sided ideal `J` of finite index.
3. **(QC) is finite gluing.** Consequently `(QC)` says: for finite quotient rings `B_+-` of `R_+-`, unitary
   representations `pi_+-` of finite quotients of `Delta_+-` dominated by `St_20(B_+-)`, and a unitary `u` intertwining
   `pi_+|Delta_0` with `pi_-|Delta_0` (a torsor under the centralizer `prod_chi U(m_chi)` of `pi_0 = pi_+|Delta_0`), the
   glued representation has `k_i` `delta`-trivial only if `z` is `eps`-trivial. Kazhdan's property (T) and residual
   finiteness of the halves add nothing beyond (1).
4. **The head is an edge invariant.** `||rho(z) - 1||_2` depends only on `pi_0 = rho|Delta_0`. With `f_1` the
   fraction of `C^d` on which the first `SL_20(F_2)` factor acts nontrivially, and a constant `c_* > 0` depending
   only on `SL_20(F_2)`,

   ```text
   c_* f_1 <= ||rho(z) - 1||_2^2 <= 4 f_1.
   ```

   So `(QC)` asks that `delta`-trivial relators force the first edge factor onto an `eps`-small share of the
   dimension.
5. **Cohn shadow: kappa never forces the head.** The assignments

   ```text
   s_1 -> e_11, s_2 -> e_21, q -> e_11     on R_+,
   t_1 -> e_11, t_2 -> e_12, q -> e_11     on R_-
   ```

   extend to ring homomorphisms `R_+- -> M_2(F_2)` that agree on `R_0`. The induced homomorphism
   `rho_M : Gamma -> GL_40(F_2)` has `rho_M(kappa) = 1` and `rho_M(z) = x_13(e_11) != 1`. Composing with the regular
   representation `λ` of the finite group `rho_M(Gamma)` gives a genuine finite-dimensional unitary representation with
   `λ rho_M(kappa) = 1` and `||λ rho_M(z) - 1||_2 = sqrt 2`, the maximum possible. The combined assignment satisfies
   every defining relation of `R` except the isometry relations `t_1 s_1 = t_2 s_2 = 1`, which it sends to `e_11`.

**Class killed (item 5).** Proofs of `(QC)`, or of the MF-radical collapse, that bound the head through `kappa`
alone, or through any finite set `W ⊆ K ∩ ker rho_M`.
- *Invariant:* the exact finite model `λ rho_M`.
- *Death step:* the inference from "`W` is `delta`-trivial" to "`z` is `eps`-trivial" for any `eps < sqrt 2`. This
  holds even with `delta = 0`.

Since `rho_M(K) = rho_M(Gamma) != 1` (compact density, `leavitt-cone-cover-kernel-is-dense-in-every-compact-model`),
some normal generator `k_i` lies outside `ker rho_M`. Every successful `(QC)` argument must pass through such a
relator. Informally, and not as a claim: these are the relators that carry the isometry relations `t_i s_i = 1`.
Those are the relations that no finite ring admits jointly with `q != 0`.

**What is not claimed.** Nothing here decides `(QC)` or `(HR)`. The open core is quantitative: whether approximate
isometry relators, in normalized Hilbert–Schmidt norm over the finite groups `St_20(B_+-)`, force `f_1 -> 0`.

## Attempts

Established; the proof is `leavitt-cone-head-bound-finite-congruence-gluing-proof`.
