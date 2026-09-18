# U2, the germ implant: Belk–Hyde–Matucci Theorem 2.1 against a Steinberg germ datum, 2026-09-18

Lane `gq-typeA-design`. The task is critic pass 3 (`research/artifacts/gq-gq-critic-pass-3.md`,
b1df416e4), untested idea U2 under S5, for the root `gl-n-q-embeds-in-fp-simple-group`.

## Verdict

- **The hypothesis the idea rests on is misread.** U2 says that "Finite presentation of
  the host needs only finitely presented local stabilizers (BHM Thm 2.1), not a finitely
  presented germ group".
  - Hypothesis (2) of Theorem 2.1 at `(M,M') = ({p},{p})` forces the germ group
    `(G)_p` to be finitely presented, at every singular point of every finite germ
    extension of `V`.
  - The reason is that the locally trivial part, the kernel `RStab_V(p)` of
    `SingFix({p},{p}) -> (G)_p`, is a simple group. So it accounts for exactly one
    relator, and the infinitely many `K_2` or scalar relations cannot be absorbed there.
  - This is `bhm-singfix-condition-forces-fp-germ-groups`, established here by lane proof.
- **What survives is the existing shell route, at one explicit input.** Take the finitely
  presented group `P = St_4(R_L)` itself as germ input, not a quotient of it.
  - For every enumeration `nu`, the shell envelope `E_nu` is simple and finitely
    generated, and it contains every `GL_n(Q)`.
  - Only finite presentation is open. That is landed as OPEN
    `steinberg-resolvent-shell-envelope-is-finitely-presented`, with route
    `gl-n-q-bh-via-steinberg-shell-envelope` into the root.
  - It is an instance of `perfect-decidable-inputs-have-fp-shell-envelopes`, provided
    the word problem of `St_4(R_L)` is decidable. That decidability is itself a
    necessary gate, and it is open.
- **Type of outcome.** The result is (b), a failing hypothesis, for the idea as stated.
  It is (a), a route with the full hypothesis check, only for the corrected form, and
  that form is conditional on one OPEN claim.

## 1. The source

- **File.** arXiv e-print of 2407.03149, fetched on the MSI login node with
  `curl https://arxiv.org/e-print/2407.03149`. It is a single gzip-compressed
  `main.tex` of 151092 bytes, last modified 3 July 2024, which is v1.
  - The SHA-256, `8fc0337eb0da9fd907c710b773e14bb4f3e7b005cf4564d0e5392e71b07a4afb`, was
    computed on MSI. It equals the hash recorded in
    `germ-complex-and-bux-gonzalez-morse-inputs-citation`.
  - A scratch copy is kept outside the repository.
- **Definition (introduction), verbatim.** "A group G ≤ Homeo(X) will be called a finite
  germ extension of B if it satisfies the following conditions:
  (1) Every element of G has only finitely many singular points.
  (2) G contains B, and indeed B is precisely the subgroup of G consisting of all elements
  that have no singular points.
  (3) For every g∈G and p∈sing(g), there exists an h∈G with sing(h)={p} such that h agrees
  with g on some neighborhood of p."
  - The source adds: "We do not actually require either of the groups B and G to be full".
- **Germs, verbatim.** "(G)_p = Stab_G(p)/RStab_G(p) where RStab_G(p) is the subgroup of
  the stabilizer Stab_G(p) consisting of elements that are the identity in a neighborhood
  of p."

### Theorem 2.1 (label `thm:SingFixFiniteness`, §2.1), verbatim

> Let X be Hausdorff space, and let G be a finite germ extension of some B ≤ Homeo(X).
> Let n ≥ 1, and suppose that:
> (1) The induced action of B on sing(G)^n has finitely many orbits, and
> (2) For every pair M ⊆ M′ of subsets of sing(G) with 0 ≤ |M′| ≤ n, the group
> SingFix_G(M,M′) ≔ {g ∈ G | sing(g) ⊆ M and g|_{M′} = id} has type F_n.
> Then G has type F_n.

The source follows with: "Note that SingFix_G(∅,∅)=B, so condition (2) includes the
hypothesis that B has type F_n."

**The exact hypotheses, for finite presentation (`n = 2`).**
- Standing: `X` is Hausdorff, `B ≤ Homeo(X)`, and `G` satisfies (1)–(3) of the definition.
  Neither `B` nor `G` has to be full.
- (1) `B` has finitely many orbits on `sing(G)^2`.
- (2) Up to `B`-conjugacy, six groups must be finitely presented:
  - `SingFix(∅,∅) = B`;
  - `SingFix(∅,{a}) = Fix_B(a)`;
  - `SingFix(∅,{a,b}) = Fix_B({a,b})`;
  - `SingFix({a},{a})`;
  - `SingFix({a},{a,b})`;
  - `SingFix({a,b},{a,b})`.
- **Not asked.** Nothing is asked of the germ groups `(G)_p`. No normality of `(B)_p`,
  and no orbit condition beyond `n = 2`. But see §3: the fourth group already forces
  `(G)_p` to be finitely presented.

### The other statements used, verbatim

- **Corollary 2.10, condition (3)** (`cor:MainFinitenessCorollary`), for comparison:
  "Either |(G)_p:(B)_p|<∞ for each p∈sing(G), or (B)_p⊴(G)_p for each p∈sing(G) and
  (G)_p/(B)_p has type F_n."
- **Theorem 1.3** (`thm:Simplicity`): "Let G be a finite germ extension of some
  B≤Homeo(X). Suppose that B is simple, locally moving, and has no global fixed points,
  and that B and G have the same orbits in X. Then the commutator subgroup G′ is simple,
  and every proper quotient of G is abelian."
- **Theorem 1.4** (`thm:Abelianization`): "Let G be a finite germ extension of some
  B≤Homeo(X), and suppose that B has no global fixed points, and that B and G have the
  same orbits in X. Then we have an exact sequence
  B/B′ ⟶ G/G′ ⟶ ⊕_{p∈R} A_p(G) ⟶ 0 where R is a system of representatives for the
  B-orbits in X. In particular, if B is perfect then G/G′ ≅ ⊕_{p∈R} A_p(G)."
  - Here `A_p(G)` is defined by the exact sequence
    `(B)_p/(B)_p′ ⟶ (G)_p/(G)_p′ ⟶ A_p(G) ⟶ 0`.
- **Appendix A** (`thm:Stabilizers`): "Let S⊂C_{d,r} be a finite set of rational points.
  Then Fix_{V_{d,r}}(S) is an iterated ascending HNN extension of V_{d,n} for some n≥1,
  and in particular Fix_{V_{d,r}}(S) and Stab_{V_{d,r}}(S) have type F∞."

## 2. The concrete germ datum

- **Base.** `B = V` on `X = C = {0,1}^N`. The singular point is `p = 0^∞`, and the
  singular set is `Ω = V·p`, the points ending in `0^∞`.
- **Local group.**
  - This is the shell construction of `shell-cantor-embeddings-are-finite-germ-extensions`,
    the repository's device for implanting an arbitrary countable group as germs at one
    point.
  - Choose a countably infinite group `P'` and a bijection `nu : P' -> N`. The group `P'`
    acts on the even shells `C_n = 0^n 1 C` through its regular action, by prefix
    replacement, and fixes `p`.
  - The germ group is `Q_nu = <germs of rho(P'), tau>`, where `(V)_p = <tau>`. It lies
    in the near permutation group of `N`.
- **Which finitely presented group maps onto the germ group.**
  - `P = St_4(R_L)`, with `R_L` the finitely presented ring of
    `leavitt-resolvent-ring-is-fp-and-contains-q`, is finitely presented
    (`steinberg-finite-presentation-and-kazhdan-theorem`).
  - Then `P * Z ↠ Q_nu`, for `P' = P`.
  - For the critic's quotient variant, `P' ∈ {E_4(R_L), PE_4(R_L)}`, a quotient of `P`,
    and `P * Z ↠ P' * Z ↠ Q_nu`.
- **Whether `GL_n(Q)` survives.** `hat : P' -> E_nu` is injective, and each germ of a
  nonidentity element is nontrivial (shell node). So `GL_n(Q)` survives exactly when it
  embeds in `P'`.
  - **`P' = St_4(R_L)`.** Yes: `one-steinberg-group-contains-every-gl-n-q`, refereed
    three times.
  - **`P' = E_4(R_L)`.** Yes. The composite `St_4(M_m(Q)) -> St_4(R_L) -> E_4(R_L)`
    equals `St_4(M_m(Q)) -> E_4(M_m(Q)) -> E_4(R_L)` by naturality. The second map is
    the restriction of the injective ring map `M_4(M_m(Q)) -> M_4(R_L)`. So the copy of
    `SL_(4m)(Q)` maps injectively.
  - **`P' = PE_4(R_L)`.** Yes. Take `4m >= n+2` and `g ↦ diag(g, det(g)^-1, 1, …, 1)`
    in `SL_(4m)(Q)`. A central element of `E_4(R_L)` lying in this copy is central in
    `SL_(4m)(Q)`, so it is `±I`. Since this image has a diagonal entry `1`, it meets
    `±I` only in `I`.

## 3. Hypothesis check at `n = 2`

| Theorem 2.1 item | For this datum | Status |
|---|---|---|
| (1) finitely many `V`-orbits on `Ω^2` | `V` is highly transitive on `Ω`: restrict prefix maps to disjoint cones and complete the table (`boone-higman-via-shell-germ-stabilizers`) | holds, for every `n` |
| (2) `SingFix(∅,∅) = V` | Higman; type `F_∞` | holds |
| (2) `SingFix(∅,M′)`, with `M′` of size 1 or 2 | `Fix_V(M')` for rational points; Appendix A `thm:Stabilizers`, type `F_∞` | holds |
| (2) `SingFix({a},{a})` | conjugate to `A_1`; finitely presented ⇒ `Q_nu` finitely presented (§3.1) | **open**; it forces the germ group to be finitely presented |
| (2) `SingFix({a},{a,b})`, `SingFix({a,b},{a,b})` | conjugate to `A_12`, `A_2`; finitely presented once `A_1` is (`shell-one-singularity-fp-forces-two-point-stabilizers-fp`) | reduces to the previous row |

So Theorem 2.1 certifies `E_nu` finitely presented exactly when `A_1` is finitely
presented. Corollary 2.10 is not available: for an input that is not virtually cyclic,
`<tau>` is neither normal nor of finite index in `Q_nu`
(`shell-isotropy-germs-fail-bhm-germ-hypothesis`). In the normal regime `GL_n(Q)`,
`n >= 3`, could not embed anyway (`normal-germ-extensions-of-thompson-v-contain-no-sl3z`).

### 3.1 The misreading

`bhm-singfix-condition-forces-fp-germ-groups` holds for any finite germ extension `G` of
`V` and any `p`, not only for shells.
- The germ map `SingFix_G({p},{p}) -> (G)_p` is onto, by condition (3) of the definition.
- Its kernel is `RStab_V(p)`, by condition (2).
- `RStab_V(p) = ⋃_W V[C − W]` is a directed union of copies of `V`, so it is simple.
- Hence `(G)_p = SingFix_G({p},{p}) / ⟨⟨k⟩⟩` for any single `1 ≠ k ∈ RStab_V(p)`.

The critic's mechanism was a germ group that is merely a quotient of a finitely presented
group, with the extra relations "sitting in the locally trivial part". That needs
infinitely many independent relators in `RStab_V(p)`, and the kernel supplies only one.
Every group is a quotient of a finitely presented group, namely a free group, so the
"quotient of an fp group" condition carries no content. The operative condition is
finite presentation of the germ group itself.

For shells, `shell-envelope-fp-forces-fp-germ-group` (lane `c-shenv`, 02ff3b8a9) already
derives a finitely presented `Q_nu` from finite presentation of `E_nu`, with no appeal
to Theorem 2.1. The present lemma covers the non-shell germ extensions that U2 also
allows.

## 4. Simplicity, and where `GL_n(Q)` lies

Theorem 1.3 hypotheses for `G = E_nu`, `B = V`:
- `V` is simple (Higman) and locally moving, and it has no global fixed point;
- `E_nu` and `V` have the same orbits, because `E_nu` contains `V` and preserves every
  `V`-orbit (shell node).

So `E_nu′` is simple, and every proper quotient of `E_nu` is abelian.

Theorem 1.4, with `V` perfect, gives `E_nu^ab ≅ ⊕_{x ∈ R} A_x(E_nu)`.
- If `x ∉ Ω`, then `(E_nu)_x = (V)_x`, so `A_x = 0`.
- For `x = p`: `Q_nu` is generated by `tau` and `rho(P')`. If `P'` is perfect, then
  `rho(P') ⊆ Q_nu′`. So `Q_nu^ab` is generated by the image of `tau`, and
  `A_p = coker((V)_p^ab -> Q_nu^ab) = 0`.
- So `E_nu` is perfect, hence simple.
- This agrees with `perfect-input-shell-envelopes-are-simple`, which has its own proof.

All three candidate inputs, `St_4(R_L)`, `E_4(R_L)` and `PE_4(R_L)`, are perfect: they
are generated by elementary elements, each a commutator. So for every enumeration,
`E_nu` is a finitely generated simple group containing `hat(P')`, and hence every
`GL_n(Q)` (§2). Simplicity is not the obstacle. Finite presentation is.

## 5. The gates on the corrected form

The corrected form is `steinberg-resolvent-shell-envelope-is-finitely-presented`.

1. **Word problem.** A finitely presented simple `E_nu` has solvable word problem, so its
   finitely generated subgroup `St_4(R_L)` does
   (`simple-envelope-forces-solvable-word-problem`).
   - `R_L` is a nonzero finitely presented simple ring, so its word problem is decidable,
     by the ring form of Kuznetsov's argument. This is a lane remark, not reviewed.
     Hence so is that of `E_4(R_L)`.
   - What is left is deciding triviality of words of `St_4(R_L)` that lie in
     `K_2(4,R_L)`. It is open.
   - The input `E_4(R_L)` passes this gate. Its finite presentation is not recorded,
     and the universal shell claims ask for finitely presented inputs.
2. **Germ group.** `Q_nu` must be finitely presented; equivalently `R_nu x_Z R_nu` is
   finitely presented, which needs `R_nu` finitely presented and the ascending HNN
   condition (`shell-germ-group-has-index-two-fiber-product`,
   `shell-germ-fp-is-an-ascending-hnn-gate`). This is open for every enumeration of this
   input. The negative benchmarks `a5-arithmetic-shell-envelope-is-not-finitely-presented`
   and `square-spiral-z2-near-shift-group-is-not-finitely-presented` show that it is a
   real restriction on `nu`.
3. **Computability.** `nu` must be computable (`shell-recursive-presentations-compute-enumerations`).

## 6. Relation to the actor verdict

`steinberg-leavitt-resolvent-groups-have-no-type-a-action` (05eb02b9f) excludes
`St_N(R_L)` as its own faithful pair-finite actor, if `K_2(N,R_L)` is central.

In a finitely presented `E_nu`, `St_4(R_L)` is an input, not an actor. `E_nu` would then
act on `Ω` with type (A):
- it is faithful, because `Ω` is dense;
- it has one orbit of two-element subsets, since `V` is highly transitive on `Ω`;
- its point stabilizers are finitely generated
  (`shell-finite-point-stabilizers-are-finitely-generated`).

By corollary 2 of `type-a-actors-have-no-infinite-virtually-central-subgroup`, every
central element of infinite order of `St_4(R_L)` has infinitely many conjugates in
`E_nu`. The two verdicts are compatible.

## 7. Critic pass 3, item 5 ((e) in the lead's list)

`unit-symmetries-of-a-core-are-graded-or-inessential` was checked at origin/main.

- **Fixed at 74de4d286.**
  - Item 4 now ends "the core is already finitely generated and the symmetry adds no
    `K_0` classes; the graded case is killed by item 2. Finite presentation of `A` is not
    addressed." That is referee-a N1 and referee-b W1.
  - The Hypothesis bullet now says that non-`σ`-simple cores are not covered (referee-b W2).
- **Left as it was.** The Scope bullet "What is closed. Designs that get finite
  presentation from a unit shift of the base or core".
  - Referee-b's W1 reading supports it: the design mechanism of gate Attempt 11 needs the
    shift only to generate the base, and item 3(b) shows the base is already finitely
    generated.
  - Under that reading the bullet is correct. Replacing "get finite presentation" by "get
    finite generation of the base" would remove the ambiguity. That is for the owning lane.
