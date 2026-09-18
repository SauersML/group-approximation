---
rg: 2
id: fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2
kind: claim
title: The Russo-BK majorant for relative susceptibility along a normal subgroup is finite exactly when the critical fibre-summed operator on the quotient is bounded
distinct_from:
  fpbs-bk-majorant-integrated-sensitivity-is-critical-l2: that bounds walk connectivity a_n on the whole graph and needs two supercritical factors for vacuity under uniqueness; this bounds chi^N on a normal subgroup, its invariant is the quotient operator norm ||S_(p_c)||_(l2(Q)) >= ||T_(p_c)||, and one supercritical factor already makes every term infinite under relative collapse.
  fpbs-percolation-kesten-normal-gap: that is the OPEN premise (alpha) of the Kesten split; this is an obstruction theorem for one class of proofs of it, not a proof or disproof.
  fpbs-fibre-summed-connectivity-operator: that is the norm comparison ||T_p|| <= ||S_p||, imported here; this shows that the Russo-BK route to the relative gap closes up exactly to finiteness of ||S_(p_c)||.
  fpbs-quotient-spectral-dt-certificates-are-subgroup-blind: that shows finite-exploration spectral certificates on Schreier quotients never beat the absolute certificate; this shows the same blindness for the differential-inequality (Russo-BK) class, with the fibre-summed critical operator as invariant.
  fpbs-relative-susceptibility-divergence-crux-fails: that gives explicit tree examples where critical relative finiteness does not give a gap; this identifies which critical quantity the Russo-BK class needs, and it is a norm rather than chi^N_(p_c).
---

**Setting.** `Gamma` is finitely generated and nonamenable, `S` is a finite
symmetric generating set with `|S|=d`, `G=Cay(Gamma,S)`, `P` is the simple
random walk operator and `p_c=p_c(G)`. Write `tau_p`, `T_p` for the two-point
kernel and `T=T_(p_c)`. `N` is an infinite normal subgroup, `Q=Gamma/N`,
`pi:Gamma->Q`, `sigma_p(q)=sum_(x in q) tau_p(o,x)`, `S_p` is convolution by
`sigma_p` on `l2(Q)`, `mu_Q=pi_*(uniform on S)` and
`chi^N_p=E_p|K_o ∩ N|=sigma_p(e)`. Define the *relative Russo-BK majorant*

```text
B^(k) = sum_(x in N) [T (P T)^k](o,x),        M^N(delta) = sum_(k>=0) (d delta)^k B^(k)   in [0,infinity].
```

By `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof` Step 4e,
this is what the integrated Russo-BK inequality produces for
`chi^N_(p_c+delta)`.

**Theorem (ESTABLISHED).**

1. *(Pushforward.)* `B^(k) = [sigma (mu_Q sigma)^k](e)` with convolution
   products on `Q`, where `sigma=sigma_(p_c)`.
2. *(Majorant forces quotient critical l2.)* If `M^N(delta)<infinity` for
   some `delta>0`, then

   ```text
   ||T_(p_c)||_(l2(Gamma))  <=  ||S_(p_c)||_(l2(Q))  <=  1/(d delta p_c).
   ```

   In particular Hutchcroft's critical l2 condition holds on `G`, so
   `p_c<p_u` on `G` by `fpbs-critical-l2-implies-nonuniqueness`, and the
   Kesten split is not needed.
3. *(Quotient critical l2 gives the majorant and the relative gap.)* If
   `||S_(p_c)||=M_Q<infinity`, then for `0<delta<1/(d M_Q)` with
   `p_c+delta<=1`,
   `chi^N_(p_c+delta) <= M^N(delta) <= M_Q/(1-d delta M_Q)`, so
   `p_c(G)<p_c(N;G)`. The radius `delta^N_*` of `M^N` satisfies
   `1/(d M_Q) <= delta^N_* <= 1/(d p_c M_Q)`, and `delta^N_*=0` iff
   `M_Q=infinity`.
4. *(One-factor vacuity under relative collapse.)* If `p_c(G)=p_c(N;G)`,
   then `sigma_s(q)=infinity` for every `s>p_c` and every `q in Q`. So every
   value at `e` of a finite convolution product of factors from
   `{delta_e, mu_Q, sigma_q : q in [0,1]}` that contains at least one factor
   `sigma_s` with `s>p_c` is `+infinity`. In particular every remainder term
   of every finite Picard iterate of the fibre-summed integrated Russo-BK
   inequality for `chi^N_q`, `q>p_c`, is `+infinity`.
5. *(Amenable quotient.)* If `Q` is amenable, then `||S_(p_c)||=chi_(p_c)=infinity`,
   so `M^N(delta)=infinity` for all `delta>0`. This is consistent with the
   Kesten premise, and it shows that the class uses nonamenability of `Q`
   only through `||S_(p_c)||`.

**The obstruction this names.** Call the *relative Russo-BK class* the
arguments that bound `chi^N_(p_c+delta)` using only Harris-FKG, Russo's
formula, BK and the critical kernel, summed over the fibre `N`.

* An argument that keeps a supercritical factor has, by (4), value
  `+infinity` in exactly the scenario it must exclude. A bootstrap would need
  a priori finiteness of some `sigma_s`, `s>p_c`, and that is premise
  (alpha) itself.
* An argument that closes up to the critical series `M^N(delta)` is finite,
  by (2), only when `||S_(p_c)||_(l2(Q))<infinity`. That already implies
  `||T_(p_c)||<infinity`, i.e. Hutchcroft's conjecture
  `fpbs-nonamenability-bounds-critical-connectivity-operator` on `G`, which
  gives `p_c<p_u` directly.

**Invariant:** `||S_(p_c)||_(l2(Q))`, which is at least `||T_(p_c)||`, with
equality for amenable `N`. **Step where every member dies:** the passage from
the critical kernel to `p_c+delta`, exactly as in the absolute case. So for
this class, proving premise (alpha) of `fpbs-bs-via-percolation-kesten-split`
is at least as hard as critical l2 on the same Cayley graph. The split
cannot transfer the difficulty of `fpbs-benjamini-schramm-universal` to
premise (beta) through a Russo-BK proof of (alpha).

*Remark (strictness, imported, not part of the theorem).* The inequality
`||T||<=||S||` can be strict. On the 6-regular tree with `N=[F_3,F_3]` one
has `||T_(p_c)||<infinity`, since trees are hyperbolic and Hutchcroft
(*Percolation on hyperbolic graphs*, GAFA 29 (2019), main theorem) gives
`p_c<p_(2->2)`. But `Q=Z^3` is amenable, so `||S_(p_c)||=infinity` by (5).

*Not covered.* Arguments that use subgraph kernels at the same `p` (the BK
coset-walk bound in the Attempts of `fpbs-percolation-kesten-normal-gap`),
exploration or martingale arguments, and anything that does not close up to
kernel products at `p_c`.

Proof: `research/fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2-proof.md`.
