---
rg: 2
id: standard-nc-stopping-theorems-miss-overlap-ledger
kind: claim
title: Standard noncommutative stopping and rounding theorems do not supply the overlapping-cut ledger
distinct_from:
  junge-riesz-bmo-does-not-close-code-newton: that audits an exact code-character martingale representation and its endpoint row estimate; this audits physical spectral cuts of the off-exact anchor-odd squares.
  one-anchor-odd-spike-has-a-cheap-reducing-cut: that proves the needed estimate for one spike; this checks whether published multi-object machinery makes those local cuts summable.
  central-adaptive-peeling-or-noncentral-stopping: that is the still-open construction; this is a source-backed fence around three tempting imports, not a proof that no stopping rule exists.
---

ESTABLISHED LITERATURE FENCE.  None of the following published theorems
supplies the selection/summability statement required by
`central-adaptive-peeling-or-noncentral-stopping` under its current
hypotheses.

1. **Cuculescu/Gundy stopping.**  The Cuculescu projections are constructed
   from one self-adjoint martingale `x_k=E_k(x)` in one increasing filtration
   `(M_k)`: recursively, `q_k` is a spectral projection of
   `q_(k-1)x_kq_(k-1)`, belongs to `M_k`, and decreases with `k`.  This
   adaptedness is what telescopes the discarded trace and the four-part
   noncommutative Gundy decomposition.  The anchor-odd squares

   ```text
   R_(a,i)=Y_(a,i)^2
   ```

   are not conditional expectations of one positive terminal operator for a
   common filtration, and their spectral projections are neither nested nor
   mutually commuting.  Declaring `M_k=W*(R_1,...,R_k)` makes the operators
   adapted but does not make them a martingale.  Replacing them by
   `E_k(sum_j R_j)` creates a martingale, but its Cuculescu cut controls the
   compressed aggregate and no longer has the spike-specific Loewner parity
   charge or the exact anchor commutation used by `(OSC5)--(OSC7)`.

   Bundling all spikes diagonally in `M_N tensor M_d` also does not close the
   gate: the stopping projection can be
   `diag(q_1,...,q_N)`, whereas physical repair requires one projection in
   `M_d` (or an orthogonal central decomposition there).  There is no
   product-projection conclusion in the cited stopping theorem.

2. **Normalized-HS almost-commuting rounding.**  Glebsky's Theorem 4 gives a
   modulus `delta(epsilon,k)` for a *fixed* number `k` of self-adjoint
   contractions when every pair has normalized-HS commutator at most
   `epsilon`.  The theorem explicitly retains the dependence on `k`.  The
   stopping family has growing cardinality and the hypotheses only bound the
   average boundary of each `R_(a,i)` against the original reflections.  They
   do not bound `[R_(a,i),R_(b,j)]`, even on average.  Therefore the theorem
   cannot be applied before paying the forbidden growing-tuple/pairwise
   conversion, and its commuting approximants would not retain the exact
   anchor grading and localized parity charge in any event.  The rank-metric
   analogue of Elek--Grabowski has the same all-pairs premise and a different
   metric; normalized-HS-small defects need not have small normalized rank.

3. **Frieze--Kannan weak regularity.**  Its output is a sum of
   `O(epsilon^(-2))` rectangular cut matrices with small residual *cut norm*.
   Those rectangles are coordinate subsets in a chosen scalar matrix basis;
   they are not projections reducing a noncommutative reflection tuple, and
   cut-norm error does not control normalized-HS relator energy.  Thus its
   Frobenius energy-increment proof supplies neither the physical
   block-diagonalization nor the no-reuse boundary ledger.

The fence is sharp rather than merely terminological.  The local spectral
coarea identity already proved in
`one-anchor-odd-spike-has-a-cheap-reducing-cut` is the one-operator analogue
of the useful part of these results.  What remains is genuinely a
multi-spike packing theorem: selected cuts must occupy disjoint physical mass
or decrease a common high-tail potential geometrically, while preserving the
anchor-specific Loewner charge.  A successful import must add exactly one of
the following hypotheses/conclusions absent above:

```text
(i) a common filtration/conditional-expectation representation preserving
    each localized parity charge;
(ii) a product-form Cuculescu projection in the physical algebra; or
(iii) an overlap inequality charging successive noncommuting cuts to one
      common square function with no factor equal to the number of spikes.
```

Primary sources checked:

* Parcet--Randrianantoanina, *Gundy's decomposition for non-commutative
  martingales and applications*, arXiv:math/0411296, especially Propositions
  1.4--1.5 and Theorem 2.1:
  https://arxiv.org/abs/math/0411296
* Glebsky, *Almost commuting matrices with respect to normalized
  Hilbert--Schmidt norm*, arXiv:1002.3082, especially Theorem 4:
  https://arxiv.org/abs/1002.3082
* Elek--Grabowski, *Almost commuting matrices with respect to the rank
  metric*, arXiv:1708.05338:
  https://arxiv.org/abs/1708.05338
* Frieze--Kannan, *Quick approximation to matrices and applications*,
  Combinatorica 19 (1999), 175--220:
  https://www.math.cmu.edu/~af1p/Texfiles/matrix.pdf
