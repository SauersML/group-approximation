---
rg: 2
id: rordam-root-propagation-one-certificates-sharp-length
kind: claim
title: One-shift traceless certificates for a row-free Rørdam root p_J need length exactly |J|+2, by a Schur-positive Porteous class
distinct_from:
  milhoj-rordam-traceless-family-quasitracial-ultraproduct: that records the Milhøj–Rørdam family and the open trace question for its ultraproduct; this proves a sharp lower and upper bound for the length of one natural class of tracelessness certificates on Rørdam roots, and shows that the bound grows with the root.
artifacts:
  - research/rordam-root-propagation-one-certificates-sharp-length-proof.md
  - experiments/rordam-one-shift-certificates-2026-09-17/porteous_class.py
  - experiments/rordam-one-shift-certificates-2026-09-17/porteous_class.out
---

**ESTABLISHED** (route `rordam-root-propagation-one-certificates-sharp-length-proof`; tier: class-killing obstruction
with a matching construction).

**Setting.** We use Rørdam's non-exact crossed product `P = D x_alpha Z` (Acta Math. 191 (2003), Section 6), built over
`Z = prod S^2` and `A = C(Z) (x) K`.
- For a finite set `J` of coordinates, `p_J` is the rank-one product Bott projection and `e_J = mu_{infty,0}(p_J)` lies
  in `D`. Rørdam's `Q` is `e_{{1}}`.
- `J` is *row-free* if `alpha_j(J)` and `J` are disjoint for all `j` (notation of Rørdam Lemma 5.4). Row-free sets
  exist in every size.
- Fix the unitary `u` with `u d u^* = alpha(d)`.
- A *one-shift certificate* of length `N` for `e_J P e_J` is a tuple `x_s = c_s u^*` with `c_s in D`, lying in the
  corner, with `||sum x_s^* x_s - e_J|| < eps` and `||sum x_s x_s^*|| <= 1 - delta`.
- Such certificates for arbitrarily small `eps` and some `delta > 0` witness tracelessness, as in Milhøj–Rørdam
  Remark 4.7 and Haagerup–Pop.

**Theorem.** Let `J` be row-free with `|J| = m`.
1. **(Obstruction.)** For `N <= m+1`, no one-shift certificate of length `N` exists, for any `delta > 0` and any
   `eps < delta`.
2. **(Construction.)** Exact certificates of length `m+2` exist, with `sum x_s^* x_s = e_J` and
   `||sum x_s x_s^*|| <= 1/2`. In particular `nu(e_J P e_J) <= m+2`, which is linear in the finiteness parameter. The
   bound `mu <= K => nu <= 2K^2` from the bus is quadratic.
3. **(Monomialization.)** Any certificate of length `N` and propagation `L` in `u` yields a *monomial* certificate
   `{d_{s,n} u^n}` of length `N(2L+1)`. This uses the conditional expectation onto `D`. The two certificate inequalities
   survive, and every monomial stays in the corner.

**Where it fails (the exact step).** A one-shift certificate descends through the composition series
`A_{-n} <| ... <| D_{-n,-1}` (quotienting by `A` and inverting `phi`, which is legitimate because
`phi(M(A))` and `A` intersect only in 0) to a stage-one certificate. That is a tuple `c_s in phi(p_J) A p_J`, which after
truncation is a section of `Hom(C^N, zeta_J^* (x) (+)_{j in F} zeta_{alpha_j(J)})`.

The two inequalities force this section to have rank at least 2 at every point. The Thom–Porteous class of the
rank-at-most-1 locus is the Schur class `s_{(N-1)^{r-1}}` of the Chern roots.
- On the slice where the coordinates of `J` are frozen, it is a Kostka-positive sum of block monomials
  `prod_K x_K^{a_K}`.
- The blocks `alpha_j(J)` are pairwise disjoint and each has at least `m` coordinates.
- So the monomial `x^lambda` survives whenever `N-1 <= m`.

A machine check (`porteous_class.py`) evaluates the full class for `m <= 2`, `r <= 4`, `N <= 4`. In all 24 cases the class
is nonzero iff `(N-1)(r-1) <= m(r+1)`, the dimension of the base, so no choice of `F` escapes it.

For `N = m+2` and `r = 2m+2` the codimension `2(m+1)(2m+1)` exceeds the base dimension `2m(2m+3)`, and a generic section
works.

**What this kills.** The Milhøj–Rørdam dichotomy says that the ultraproduct of roots is traceless iff certificate length
stays bounded. For root families with `|J| -> infinity`, **no bounded-length certificate can consist of shift `-1`
monomials `c u^*`**, whatever the coefficients in `D` are and at whatever inductive-limit stage they live. By item 3, every
certificate monomializes. So a bounded-length certificate for large `|J|` must contain monomials of some shift other
than `-1`, and it cannot be split into its shift `-1` part plus a remainder that is itself a certificate.

For shift `-s` the descent of Steps 1–2 still lands in `phi^s(p_J) A p_J`. The target blocks
`alpha_{j_s} ... alpha_{j_1}(J)` then share the sets `I_j`, so the disjoint-block Schur positivity of Step 4 must be
replaced by a Hall-deficiency count. This is the precise next step.

**Scope (honest).**
- The theorem is about the corners `e_J P e_J` with `J` row-free. It is not about the Milhøj–Rørdam `P_n = M_q(ePe)` with
  `e = phi(e_11)`. Matrix amplifications replace the rank-one domain `zeta_J` by `zeta_J^{(+)q}` and are not covered.
- That `M_t(e_J P e_J)` stays finite for `t <= m` is expected from `m` disjoint transversals and Rørdam Lemmas 6.2–6.5,
  but is not claimed here.
- Shift `+1` monomials (`x = d u`, with `d in e_J D alpha(e_J)`) are not covered either. There the domain `alpha(e_J)` is
  an infinite projection at every stage, and the problem is a fractional comparison `phi(P) <=_frac (1/2) (+)^N P`
  between infinite-rank bundles. It is open whether a Hall-deficiency version of the same Schur positivity blocks it.

## Attempts

- 2026-09-17 (sw-129): proof as in the route. The first falsifiable step, the nonvanishing of the Porteous class for
  small `(m, r, N)`, was machine-checked before the write-up.
