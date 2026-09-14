---
rg: 2
id: subshift-el3-rigid-supports-proof
kind: route
title: Spans of rigid subgroups are corner rings, and corners of a minimal subshift algebra have centre F_2
target: subshift-elementary-group-rigid-supports-are-mutual-centralizers
requires: []
artifacts:
  - research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md
---

Direct proof (artifact §3).

**1.** `G_U ∋ e_ij(r)` for `r ∈ e_U R e_U` and `i ≠ j`. The identity `(g−I)(h−I) = (gh−I) − (g−I) − (h−I)` makes the
span a ring, and `(E_ij r)(E_ji s) = E_ii rs`, so the span is all of `M_3(e_U R e_U)`.

Centre of the corner. Let `c = Σ_j f_j u^j` be central in `e_U R e_U`, so `supp f_j ⊆ U ∩ T^j U`.
- For clopen `V ⊆ U`, `e_V c − c e_V = Σ_j f_j(e_V − e_(T^jV)) u^j`.
- `T` has no periodic points. So for `x ∈ supp f_j` with `j ≠ 0`, some `V ⊆ U` contains `x` but not `T^(-j)x`, which
  forces `f_j(x) = 0`. So `c = f_0 ∈ LC(U)`.
- Commuting with `e_U u^j e_U = e_(U∩T^jU) u^j` makes `f_0` invariant under the returns, so constant on `U ∩ (orbit)`.
  Orbits are dense and `f_0` is locally constant, so `f_0` is constant.
- The same separation shows `LC(U)` is maximal commutative in `e_U R e_U`.

**2.** If `h` centralizes `G_U`, it commutes with `M_3(e_U R e_U) ∋ E_U`. So it is block diagonal, and its `U`-corner
is central in `M_3(e_U R e_U)`, hence `c E_U` with `c ∈ F_2`. Invertibility gives `c = 1`, so `h ∈ G_(X∖U)`.
Elements supported on disjoint clopen sets satisfy `(g−I)(h−I) = 0 = (h−I)(g−I)` and commute.

**3.** `span(GL_3(F_2) − I)` is a nonzero ideal of the simple ring `M_3(F_2)`, so `span(L_(X∖U) − I) = M_3(e_(X∖U)A)`.
Let `h` centralize `L_(X∖U)`.
- `h` is block diagonal, and its `X∖U` corner is `cI_3` with `c` commuting with `e_(X∖U)A`.
- So `c ∈ LC(X∖U,F_2)` by maximal commutativity, and invertibility gives `c = e_(X∖U)`, so `h ∈ G_U`.

**4.** A normalizer of `G_U` preserves its span `M_3(e_U R e_U)`, hence the unit `E_U`. Conversely, commuting with `E_U`
preserves `I + M_3(e_U R e_U)`. The commutant of all `E_U` in `M_3(R)` is `M_3(C_R(A)) = M_3(A)`, and
`G ∩ GL_3(A) = GL_3(A) = EL_3(A) = L`.

**5.** `span L = M_3(A)`, so `N_G(L)` preserves `M_3(A)` and its centre `D`. Let `g` normalize `D`, with
`g(fI)g^(-1) = (f∘φ^(-1))I`.
- Entrywise `g_ij = Σ c_n u^n` gives `c_n(f∘T^(-n) − f∘φ^(-1)) = 0`, so `φ^(-1) = T^(-n)` on `supp c_n`.
- These clopen supports cover `X`: otherwise `e_V g = 0` for some clopen `V ≠ ∅`, and `e_V = e_V g g^(-1) = 0`.
  So `φ ∈ [[T]]`.

Lower bound:
- `diag(a,a^(-1)) = w(a)w(−1)` with `w(a) = e_12(a)e_21(−a^(-1))e_12(a)`, so `diag(a,a^(-1),1) ∈ E_3(R)`.
- `diag([b,c],1,1) = diag(b,b^(-1),1)·diag(c,1,c^(-1))·diag(b^(-1),b,1)·diag(c^(-1),1,c)`, so `diag(a,a,a) ∈ G` for
  `a ∈ [R^×,R^×]`.
- `γ ↦ a_γ` is a homomorphism `[[T]] → R^×` with `a_γ f a_γ^(-1) = f∘γ^(-1)`. So `diag(a_γ,a_γ,a_γ)` normalizes `L`
  and induces `γ ∈ [[T]]'`.

Finally `g e_V(l−I) g^(-1) = e_(φ(V)) g(l−I)g^(-1)` gives `g L_V g^(-1) = L_(φ(V))`.
