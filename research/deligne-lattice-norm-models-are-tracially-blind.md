---
rg: 2
id: deligne-lattice-norm-models-are-tracially-blind
kind: claim
title: Every corona model of a Deligne cover can be padded, without changing its central kernel, to one whose tracial shadow is the fixed finite-residual character
distinct_from:
  hs-invisible-corona-maps-are-full-trace-paddings: that characterizes the HS-invisible corona maps of any countable group as identity paddings; this pads with regular representations of finite quotients instead, so the padded model stays faithful off the finite residual, and it draws the consequence for the MF radical of the Deligne covers.
  hs-invisibility-inflation-no-go: that inflates by identity blocks until every element is HS-invisible; this keeps every element outside the finite residual separated in norm, and fixes the shadow to the character of the finite residual.
  deligne-maslov-tensor-functors-are-asymptotically-regular: that proves the shadow of any 1/3-model is regular off the center; this shows the central part of the shadow is also forced, to the indicator of <z^2>, independently of what the model does to z^m in norm.
  deligne-cover-compression-defects-are-trivial: that kills compression-defect criteria through a source-side quasimorphism invariant; this kills trace-side criteria through the shadow invariant.
  deligne-norm-parameter-group-embeds-in-ce-subgroup: that proves what tracial data can give (finiteness of P_op); this proves what it cannot give (the MF radical of the lattice), and names the corner data that escapes.
---

**ESTABLISHED** (route `deligne-lattice-norm-models-are-tracially-blind-proof`). Unreviewed.

**Setting.**
- Let `1 <= q <= infinity`, and let `E_q = Gamma~ / <z^q>` be the Deligne cover of `Gamma = Sp_4(Z)`. Here
  `E_infinity = Gamma~`.
- Let `R_q = Res_fin(E_q)`. By `deligne-covers-of-sp2g-z-have-finite-residual-2z`, `<z^2> <= R_q <= <z>`, with
  equality `R_q = <z^2>` for finite `q >= 3`.
- A corona model is a homomorphism `Theta : E_q -> U(Q)` with `Q = prod_n M_(d_n) / (+)_n M_(d_n)`. Its lifts are
  unitaries `theta_n(x) in U(d_n)`.
- Its *shadows* are the ultralimit characters `tau_w(Theta(x)) = lim_w tr theta_n(x)`, and more generally the
  tracial-ultraproduct representation `Theta^w : E_q -> U(M^w)`.

**Theorem.**
1. **(TB1) Padding.** For every corona model `Theta` there is a corona model `Theta'` with the following
   properties:
   - `ker Theta' = ker Theta cap R_q`. In particular, `Theta'(z^m) = 1` iff `Theta(z^m) = 1` for every `m` with
     `z^m in R_q`.
   - Every shadow of `Theta'` equals the indicator `1_(R_q)`. The tracial ultraproduct `Theta'^w` factors through
     the residually finite group `E_q / R_q`, and is its left regular trace pulled back.
   - The normalized-HS defect of every lift of `Theta'` is `o(1)` times the operator-norm defect of `Theta`.
   - `Theta` is the compression of `Theta'` to a projection `P` of the commutant of `Theta'(E_q)` with
     `tau_w(P) = 0` for every `w`.
2. **(TB2) Blindness.** Let `I` be any invariant of corona models that depends only on the tracial ultraproduct
   data. Examples are the character, the trace-preserving isomorphism class of `(Theta^w, M^w)`, spectral measures
   of `Theta^w(x)`, normalized-HS defects and distances, and normalized winding numbers. Then `I(Theta')` does not
   depend on `Theta`. Hence, for every `m`:

   ```text
   z^m in Rad_MF(E_q)   iff   z^m in ker Theta for every model Theta whose shadow is 1_(R_q).
   ```

   The fixed shadow `1_(R_q)` is the shadow of the honest representation `Lambda = (+)_j lambda_(E_q / N_j)`, which
   kills `R_q`. So `Rad_MF` is invisible to the shadow invariant: on a single shadow class it can take every value
   allowed for the full problem.

**Class killed.** Any proof that `z^m in Rad_MF(E_q)` (for `q = infinity`: that `Gamma~` is not MF) is killed if it
runs as follows: first establish a property of the shadow, or of normalized trace or HS data, of an arbitrary
model, then conclude norm-triviality `Theta(z^m) = 1` from it.
- *Invariant.* The shadow `1_(R_q)` of the padded model.
- *Death step.* "shadow property ==> `Theta(z^m) = 1` in `Q`". The padded model has the same shadow as `Lambda`,
  while its norm kernel on `R_q` is that of an arbitrary `Theta`.
- *Members.* The class includes:
  - character rigidity and trace classification, such as `deligne-maslov-sector-traces-are-central-regular`;
  - HS-stability or flexible-stability rounding of the whole model, which yields only a normalized-HS-close honest
    representation, and honest representations kill `R_q` anyway by Malcev;
  - normalized-HS defect gaps and HS-metric ladders;
  - normalized spectral measures of `Theta(z)`;
  - normalized windings;
  - tensor and sum functors read through `tr`.
- *What escapes.* Two kinds of data are not normalized-trace data and are not killed:
  - data that see corners of vanishing trace, such as the commutant corner `P` of (TB1), i.e. corner extraction
    `(CPE*)` of `commutant-projection-extraction`;
  - rank-unnormalized data, such as unnormalized Schatten defects, which are unchanged by padding because the
    regular blocks have zero defect.

**Consequence for `deligne-universal-cover-lattice-is-not-mf`.** A proof must use corner or unnormalized data. The
tracial route reaches only finiteness of `P_op` (`deligne-norm-parameter-group-embeds-in-ce-subgroup`). The
remaining step from finite `P_op` to non-MF of `Gamma~` is exactly corner extraction, which is invisible to the
shadow by (TB1).
