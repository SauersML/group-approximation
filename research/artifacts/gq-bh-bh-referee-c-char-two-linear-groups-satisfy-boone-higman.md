# Referee C (end-to-end, adversarial) — `char-two-linear-groups-satisfy-boone-higman`

**Verdict: PASS-with-fixes.** The chain from "finitely generated linear group over a
field of characteristic two" to "subgroup of the finitely presented simple group
`(L^(⊗d))^x`" is logically complete at the level of node statements. No
"virtually BH ⇒ BH", "subgroup ⇒ BH" or quotient step is used without a node. The
claim is honest that it is not independently reviewed. Its conditionality should,
however, be in the status line (F1), and two nodes carry a false statement about
Zaremsky (F2).

Scope of this review: node statements, the route, artifact
`boone-higman-leavitt-tensor-hosts-2026-09-12.md` §§3, 7, 8.3, and the statuses of
every node the route requires. I re-derived Lemma 7.1 and Theorem 7.2 in full. I
checked the Farrell–Jones step only structurally, at hypothesis level; see item 4.
I read no primary source (Khanh, Bartels–Lück, ABC) myself.

## 1. The input reduction (Theorem 7.2) — checked, correct
- `H <= GL_n(K)` finitely generated. The entries of the generators and their
  inverses generate a finitely generated field `F` over `F_2`, of transcendence
  degree `d`.
- `d = 0`: `F` is finite, so `H` is finite and embeds in `GL_N(F_2) <= M_N(L)^x ≅
  L^x`. This uses `M_N(L) ≅ L` for every `N`, which holds for `L = L(1,2)` since
  `gcd(N, 2−1) = 1`.
- `d >= 1`: `F` is finite of degree `m` over `F_2(t_1..t_d)`. The regular
  representation gives `H <= GL_(nm)(F_2(t))`. A common denominator `h` of the
  finitely many entries gives `H <= GL_(nm)(F_2[t][1/h])`.

## 2. Lemma 7.1 (unital embedding `F_2[t_1..t_d][1/h] -> L^(⊗d)`) — checked, correct
- `d = 1`: `f = t·h` is monic, since every nonzero polynomial over `F_2` is monic.
  `F_2[g^±][T]/(f(T) − g) ≅ F_2[T][1/f(T)]`, and it is free over `F_2[g^±]` with
  basis `1..T^(deg f − 1)`. The regular representation is a unital injection into
  `M_(deg f)(F_2[g^±])`.
- `d >= 2`:
  - `h ∈ C_0[t_d]` has leading coefficient `c`. If `deg_(t_d) h = 0`, then `c = h`
    and `f = t_d`. Put `f = t_d h/c`, which is monic.
  - `1/h = t_d/(c f)` gives the inclusion into `C[t_d][1/f]` with `C = C_0[1/c]`.
  - The same monic presentation gives a unital injection into `M_(deg f)(C[g^±])`.
  - `C` embeds by induction, applied to `c`, and tensor products of injections
    over a field are injective.
- **Input used:** the Thompson-unit embedding `F_2[g^±] -> L`, i.e. a unit
  `g ∈ L` with no polynomial relation. It is cited from the curve/Laurent nodes. I
  did not re-check it.

## 3. The host — checked at statement level
- `L^(⊗d) = B ⊗ L` with `B = L^(⊗(d−1))`, which is central simple (a tensor
  product of central simple algebras over a field) and finitely presented.
- `central-simple-leavitt-tensor-unit-groups-are-simple` (2) needs `B` central
  simple and `K_1 = K_2 = 0`. It gives `R^x ≅ GL_3(R) = E_3(R)`, which is simple.
  The centre is `F_2`, so there are no nontrivial central scalars.
- `leavitt-tensor-hosts-acyclic-steinberg-and-fp` (2, 3) needs `B` simple and
  finitely presented and `K_1 = K_2 = 0`. It gives `St_r(R) ≅ GL_r(R)` for
  `r >= 3`, hence `R^x ≅ GL_r(R) ≅ St_r(R)`, which is finitely presented.
- The earlier referee report
  (`review-boone-higman-leavitt-tensor-hosts-2026-09-12.md`) passed both nodes,
  with Khanh as a trust surface.

## 4. `K_1 = K_2 = 0` for `d >= 3` — structural check only
`leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees` is a lane
derivation and is **not independently reviewed**. At hypothesis level:
- **Crossed product.** A degree-one unit exists. In `L ⊗ L'`,
  `u = s_1⊗t'_1 + s_2⊗t'_2` has inverse `v = t_1⊗s'_1 + t_2⊗s'_2` (`uv = vu = 1`,
  checked). So `L^(⊗d)` is a (twisted) crossed product `C ∗ Z^(d−1)` over
  `C = L_0^(⊗(d−1)) ⊗ L`, as `leavitt-tensor-powers-are-twisted-crossed-products`
  asserts. This is consistent.
- **The coefficient ring.** `C` is a directed union of `M_N(L)` along free
  (block-diagonal) inclusions.
  - `L` is hereditary, so `C` is coherent with weak dimension at most 1, i.e.
    semihereditary, i.e. regular coherent.
  - `K(C) = colim K(M_N(L)) = 0` by ABC.
  - Both are consistent with `leavitt-crossed-product-coefficient-ring-is-k-trivial`.
- **The Farrell–Jones step.** Farrell–Jones for `Z^(d−1)` with coefficients in
  additive categories (twisted crossed products included) reduces to `C ∗ V` for
  `V ≤ Z^(d−1)` cyclic, i.e. to twisted Laurent rings `C_φ[t^±]`. By twisted
  Bass–Heller–Swan and Waldhausen's Nil vanishing for regular coherent `C`, these
  are `K`-trivial.
- **What that needs.** Only regular coherence of `C` itself. The node's extra
  claim that `C[Z^m]` is regular coherent (it notes Bartels–Lück record that
  inheritance as open in general) appears unnecessary for the `Z^(d−1)` case. The
  owner should check whether the route leans on it; if it does, that step needs
  its own justification.
- **Recommendation.** A proof-gap review of
  `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof` by gq-referee-a, and
  a citation review (Bartels–Reich coefficients, Waldhausen, Bartels–Lück) by
  gq-referee-b, before this class result is relayed as refereed.

## 5. Fixes
- **F1 (status honesty).** The status line reads "ESTABLISHED (2026-09-12) …
  Not independently reviewed". It should also name the two conditions in the line
  itself:
  - Khanh arXiv:2609.08428v1, an unrefereed preprint behind
    `leavitt-tensor-hosts-acyclic-steinberg-and-fp`;
  - the unreviewed Farrell–Jones derivation (item 4).

  At present they are visible only in Attempt 3.
- **F2 (false statement).** `char-two-surface-linear-groups-satisfy-boone-higman`
  and artifact `boone-higman-leavitt-tensor-hosts-2026-09-12.md` §8.3 say
  "Zaremsky arXiv:2405.09722 settles GL_n(Q)". That is wrong: Zaremsky (Theorem
  1.2) covers finitely generated subgroups of `GL_n(Q)`, and `GL_n(Q)` itself is
  open (`gl-n-q-embeds-in-fp-simple-group`; BBMZ p. 7). The claim node was
  corrected at 2598812b3; these two places were not.
- **F3 (optional; trust reduction).** Finite presentation of `R^x` can go through
  `St_5(R) ≅ GL_5(R) ≅ R^x` and the refereed
  `steinberg-groups-of-fp-rings-are-fp-in-rank-five`, instead of Krstić–McCool.
  That removes one import.
- **F4 (priority).** The novelty check was a bounded web search on 09-12.
  "Boone–Higman for all f.g. linear groups in characteristic two" should be
  checked against the literature by bh-lit before it is relayed as new.
