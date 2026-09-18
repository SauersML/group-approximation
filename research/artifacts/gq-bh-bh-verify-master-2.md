# bh-verify-master, item 2: `decidable-host-classes-reduce-to-canonical-kazhdan-groups`

Adversarial check by lane bh-verify-master, 2026-09-18, read on origin/main at 6481dbd30 (node landed in
87daac9eb). This is a lane check, not an external review.

**Verdict: PASS.** Theorems 1–3 are correct as stated. Their only load-bearing import is
`fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`, which is ESTABLISHED and was referee-repaired
(ref-01, 2026-09-17). There, `Γ` embeds via `δ_0(Γ) ≤ [Δ,Δ]` and `ℓ ↦ diag(u_ℓ,1,1)`, and
`WP(Γ) ≤_m WP(H) ≤_T WP(Γ)`.

**Theorem 1 (canonical inputs).**
- (a)⇒(b)⇒(c) is immediate, since `H_Γ` is infinite, finitely generated, simple, Kazhdan and decidable
  when `Γ` is.
- (c)⇒(a) holds because `Γ ≤ H_Γ`.
- No closure property of `𝒦` is used. **Correct.**

**Theorem 2.**
- Items 1, 2, 4 and 5 are Theorem 1 applied to the named classes.
- Item 3 also uses (1)⟺(2) of `boone-higman-iff-fp-just-infinite-hosts`. That node is ESTABLISHED with a
  route.
  - Its statement 2 quantifies only over infinite inputs.
  - Finite groups embed in infinite decidable groups, so nothing is lost.
- **Correct.**

**Theorem 3 (Kazhdan filter).**
- **The argument.** It needs one infinite decidable `Γ` (for example `Z`). If `H_Γ` embedded in a
  𝒫-group, subgroup closure would give 𝒫 to `H_Γ`, which is infinite, simple and Kazhdan.
- **The listed properties are all subgroup-closed and fail for such groups:**
  - amenable: (T) plus amenable gives finite;
  - Haagerup: (T) plus Haagerup gives finite;
  - residually finite: infinite fg simple groups are not RF;
  - finite Kazhdan subgroups, and RF fg simple subgroups: immediate.
- **Correct.**

**Host exclusions.**
- **Stated as cited:**
  - Thompson's F, T, V and the Higman–Thompson groups are Haagerup (Farley; cube complexes).
  - Every group acting properly on a CAT(0) cube complex is Haagerup (Niblo–Reeves).
  - Linear and self-similar groups are residually finite.
- **Burger–Mozes and Wise lattices** are Haagerup because they act properly on products of trees, which
  are square complexes. Hence they have no infinite Kazhdan subgroups. Consistent.

**Remark.**
- `L_(F_2)(1,2)` has `L ≅ L²`, hence `L ≅ L³`, as right modules. So `M_3(R ⊗ L) ≅ R ⊗ L`.
- `R → R ⊗ L` is unital and injective over a field.
- So `EL_3(R_Γ) ≤ GL_3(R_Γ ⊗ L) ≅ (R_Γ ⊗ L)^×`. **Correct.**

**Nits (no fix needed).**
- **Wording.** The "more precisely" sentence of Theorem 3 says "`H_Γ` with `Γ` infinite". `H_Γ` is
  infinite for every `Γ`, since `C(Γ)` is infinite, so the qualifier is harmless but unnecessary.
- **Scope.** The node's statement that the Kazhdan filter "accounts for" the listed kills is about
  *universality* only. It does not reprove those kills for individual inputs. The node says so implicitly
  ("as universal").

## Lesson for general BH

Universality of a host class is decided on one explicit family,
`EL_3(LC(2^{C(Γ)}, F_2) ⋊ (Z/2 ≀ C(Γ)))`. The check confirms that this is a formal consequence of an
established, referee-repaired host lemma, not a new assumption. Any candidate universal host can be tested
first against a single `H_Z`, before any finiteness work.
