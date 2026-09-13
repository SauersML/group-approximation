---
rg: 2
id: z2-o2-actions-anti-inner-and-o3-rokhlin-criterion
kind: claim
title: An outer Z/2-action on O_2 with crossed product O_2 is approximately inner by anti-invariant unitaries, and it is Rokhlin iff strongly approximately inner iff O_3 embeds unitally in its fixed central sequences
distinct_from:
  o2-central-sequence-k-theory-bi-cyclotomic-transfer: that proves the two transfer identities and the dynamical reading of fixed points for any finite abelian group; this specializes to p = 2, where the identities force both dual actions to be −1 and so produce an implementing unitary from K-theory alone.
  outer-zp-actions-on-o2-are-strongly-approximately-inner: that is the open question whether invariant implementing unitaries exist; this proves anti-invariant ones exist whenever the crossed product is O_2, and reduces the open question to a unital copy of O_3.
  o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences: that characterizes the Rokhlin property by a unital O_2 in the fixed central sequences; this shows that at p = 2 a unital O_3 already suffices, given Izumi's theorem.
  zp-o2-generator-kk-class-is-twisted-asymptotic-innerness: that proves through Gabe–Szabó uniqueness in KK^G that a contractible crossed product is equivalent to odd asymptotic innerness along continuous paths; this derives sequential odd innerness from transfer in central-sequence K-theory with no uniqueness theorem, and adds that strong approximate innerness is a unital O_3 in the fixed central sequences.
  zp-o2-contractible-crossed-product-only-coboundaries: that proves for every prime, from Izumi and Gabe–Szabó 5.14, that a central eigen-unitary of a nontrivial character is equivalent to the Rokhlin property; this shows at p = 2 that such a unitary exists iff 2[1] = 0, iff a unital O_3 sits in the fixed central sequences.
---

**ESTABLISHED (derivation; unreviewed).**  Let `α : Z/2 ↷ O_2` be pointwise
outer with generator `σ`.  Write:
- `A = O_2`;
- `F^α = (A_∞ ∩ A')^α`;
- `M_* = K_*(F^α)`.

Use the operators `φ` (the nontrivial character) and `ψ` (the generator) of
`o2-central-sequence-k-theory-bi-cyclotomic-transfer`.

1. **Always.**  `φ = −1` on `M_*`.  So `[vv*] = −[1]` for every
   anti-invariant isometry `v ∈ A_∞ ∩ A'`.  The following are equivalent:
   - `α̂` is strongly approximately inner;
   - `A_∞ ∩ A'` contains an anti-invariant unitary;
   - `2[1] = 0` in `K_0(F^α)`;
   - `O_3` embeds unitally into `F^α`.
2. **Contractible crossed product.**  Suppose `O_2 ⋊_α Z/2 ≃_KK 0`.  Then also
   `ψ = −1` on `M_*`.
   - **(a) Anti-inner.**  There are unitaries `w_n ∈ O_2` with
     `‖σ(w_n) + w_n‖ → 0` and `w_n* a w_n → σ(a)` for all `a ∈ O_2`.
     Equivalently, `(O_2 ⋊ Z/2)_∞` contains a unitary `W` that commutes with
     `O_2` and satisfies `u W u* = −W` and `α̂(W) = −W`.
   - **(b) One criterion.**  The following are equivalent:
     - `α` has the Rokhlin property;
     - `α` is strongly approximately inner;
     - `α̂` is strongly approximately inner;
     - `2[1] = 0` in `K_0(F^α)`;
     - `O_3` embeds unitally into `F^α`;
     - `M_* = 0`.

     Transfer alone gives the equivalence of the second through fifth bullets.
     Izumi's theorem is used once, to get from strong approximate innerness to
     the Rokhlin property.
3. **Detection at `p = 2`.**  By item 3 of
   `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, detection at `2` is
   equivalent to the following.  For every outer `Z/2`-action on `O_2` whose
   crossed product is `O_2`, `O_3` embeds unitally into the fixed central
   sequences.
   - Item 2(a) says each such action is already strongly approximately inner
     up to a sign.  Its implementing unitaries can be taken anti-invariant.
   - The open question of Barlak–Li II, Remark 4.14(2), restricted to these
     actions, is whether the sign can be removed.
   - The obstruction is `2[1] ∈ K_0(F^α)`.  Multiplying `w` by an
     anti-invariant central unitary removes the sign, and such a unitary exists
     iff `2[1] = 0`.
4. **Odd primes.**  For `p` odd with contractible crossed product, no single
   twisted form is forced.  The only relation of this kind is
   `Π_(k∈(Z/p)^×) (1 − φ_(χ_0^(−k)) ψ_(g_0)) = 0` on `M_*`.  For `p = 2` the
   product has one factor, `1 − φψ`, and that is item 2(a).

**Reading.**  At `p = 2`, the two transfer identities are `1 + φ = 0` and
`1 + ψ = 0`.
- The unique anisotropic line of `Ĝ × G` then acts trivially, which gives the
  anti-invariant implementing unitaries.
- The two isotropic lines act by `−1`.
- The open part is whether the isotropic operators `φ` and `ψ` also fix `[1]`,
  which happens iff `[1] = −[1]`.

**Relation to peer nodes (lane ex2-uct-unit-class-cohomology, landed after
this node).**
- Item 6 of `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness` proves,
  through Gabe–Szabó Theorem 5.8, the asymptotic form of item 2(a) together with
  its converse.  Here the converse is: odd asymptotic innerness forces
  `O_2 ⋊ Z/2 ≅ O_2`.
- The two proofs are independent: KK^G uniqueness there, central-sequence
  transfer and Cuntz comparison here.  So they cross-check each other.
- Item 5 of `zp-o2-contractible-crossed-product-only-coboundaries` is the
  eigen-unitary criterion for every prime.  At `p = 2`, item 1 above
  identifies it with `2[1] = 0` and with a unital `O_3`.
- None of those nodes has the `O_3` form.

**Model tests.**
- *Rokhlin model* `μ = ⊗_n Ad(diag(1, −1))` on `O_2 ⊗ M_(2^∞)`.  Put
  `w_n = diag(1, −1)^(⊗n) ⊗ σ_x` in factor `n + 1`.  Then `σ(w_n) = −w_n`, and
  `Ad(w_n*)` agrees with `μ` on the first `n` factors.  All of item 2(b) holds,
  and `M_* = 0`.
- *Outerness is needed in 2(a).*  Take `σ = Ad(u)` with `u = u* ∈ U(O_2)`.  Its
  crossed product `O_2 ⊗ C^2` is contractible.  If `w* a w = u a u*` for all
  `a ∈ O_2`, then `w = u* c` with `c` a central sequence.  Such a `c` commutes
  with `u`, so `σ(w) = w`, which is never `−w`.  So anti-inner fails.
- *Item 1 needs no crossed-product hypothesis;* item 2 does.  The inner action
  above shows that dropping outerness breaks item 2.

No priority is claimed for item 1's first two bullets (Izumi's duality in
central-sequence form).  The forced sign (items 1 and 2(a)) and the `O_3`
criterion were not found in Barlak–Li II or in the sources cited by the
predecessor nodes.  This was a bounded check, not a literature search.

Proof: `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion-proof`.
