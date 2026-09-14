# sk-rfd-amalgam plan: missing input 1 of the Popa comb plan (2026-09-14)

Lane sk-rfd-amalgam, wave 12. Target: missing input 1 of `weakly-dense-popa-combs-exist-in-property-t-factors` (research/artifacts/sk-popa-lgx-2026-09-13-part1.md §3).
- Question: is `U_{i+1} = ((U_i ⊕ M_{d_i}) *_{C²} M_{r_i}) * C(T)` residually finite-dimensional whenever `U_i` is?
- The amalgam `C²` sits in `V_i = U_i ⊕ M_{d_i}` as `{(1,0),(0,1)}`, with tooth `e_i = (0,1)`. In `M_{r_i}` it sits as `{1−p, p}`, with p minimal.

## Literature located (bounded search, 2 web searches)
- Q. Li and J. Shen, *A note on unital full amalgamated free products of RFD C*-algebras*, Illinois J. Math. 56 (2012), no. 2. Per the search record, it gives a necessary and sufficient condition for `A *_F B` to be RFD over a finite-dimensional `F`, stated through inclusions into (ultra)products of matrix algebras that agree on F. It also has an example of RFD algebras whose amalgamated free product is not RFD. **Statement to be quoted at source before use.**
- S. Armstrong, K. Dykema, R. Exel and H. Li, *On embeddings of full amalgamated free product C*-algebras*, Proc. Amer. Math. Soc. 132 (2004), 2019–2030, arXiv:math/0210448. The criterion for finite-dimensional A, B, D. It covers only the finite-dimensional case, a check on the general criterion.
- R. Exel and T. Loring (1992): free products of RFD algebras are RFD. This settles the `* C(T)` step.
- A. Korchagin, arXiv:1206.4970: amalgamated free products of commutative C*-algebras are RFD. Not our case.

## Planned reduction
1. **Necessity is trivial.** An embedding of `A *_F B` into `∏_k M_{n_k}` restricts to embeddings of A and B that agree on F.
2. **Construction for our A, B, F.** Let `ρ_k` be a faithful family of finite-dimensional representations of `U_i`, of dimension `D_k`. Put
   - `σ_k = ρ_k^{⊕(r−1)d_i} ⊕ (id_{M_{d_i}} ⊗ 1_{D_k})` on `C^{n_k}`, with `n_k = r d_i D_k`;
   - `τ_k(x) = x ⊗ 1_{d_i D_k}` for `x ∈ M_r`.

   `σ_k(e)` and `τ_k(p)` both have rank `d_i D_k`, so after a unitary change of basis σ_k and τ_k agree on `C²`. Both families are faithful.
3. **If the Li–Shen criterion is exactly** "exists faithful families into ∏ M_{n_k} agreeing on F", then `V_i *_{C²} M_r` is RFD, and `* C(T)` keeps it RFD by Exel–Loring.
4. **Consequence for input 2.** A finite-dimensional representation of `V_i` extends to `U_{i+1}` iff `dim(1−e) = (r−1)·dim(e)`: choose matrix units of M_r with p ↦ e, and any unitary for C(T). So input 2 is multiplicity bookkeeping.

## Checks before any claim
- Quote Li–Shen's theorem verbatim: product vs ultraproduct, embedding vs inclusion, unital, separability, and whether the agreement on F is exact or up to unitary equivalence.
- Model-test the example where RFD A, B give a non-RFD amalgam, to see where rank ratios fail. Cross-check with ADEL in the finite-dimensional case (for example `M_2 *_{C²} M_3` with p of rank 1 in both is not RFD, since the ratio 1/2 ≠ 1/3).
