# Zaremsky Problem 1.1, positive side: status, reductions, and the defect calculus for higher ropes (2026-09-13)

Lane z1-01-embed-pos. Root: `zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`.
Everything in §4 and §6 is UNREVIEWED research notes. §1–§3 and §5 record read
sources, landed nodes and standard homological algebra.

## 1. Status and sources

- Zaremsky, *Some open problems* (July 12, 2026), §1 Problem 1: "Does every group of type F_n embed in
  a group of type F_{n+1}, for n ≥ 2? What about in a group of type F_∞?"
- Fournier-Facio–Zaremsky, *Finiteness properties and Higman's rope trick*, arXiv:2607.21727v1
  (23 July 2026), read from the arXiv HTML on 2026-09-13.
  - Introduction: "A fundamental open question (see [Bes], Q 8.7, [KM], 21.146, [Zar], 1.1, and the
    comments to [Ago]) is whether the theorems of Higman and Leary admit higher-dimensional analogues."
    [Bes] = Bestvina, *Questions in geometric group theory*; [KM] = Kourovka Notebook; [Ago] =
    MathOverflow q/60565.
  - Question 1.3: "Does every finitely generated recursively presented group embed in a group of type F_3?
    In a group of type F_∞?"
  - Question 1.4: "Does every finitely generated group embed in a group of type FP_3? In a group of type
    FP_∞?"
  - Theorem A (node `fournier-facio-zaremsky-rp-fp-n-hosts-give-f-n-hosts`), Lemma 2.1 (finitely
    presented + FP_n ⇒ F_n), Theorem B (node `higman-rope-trick-group-is-never-fp3`), Remark 3.5
    (the rope trick depends on F being free, including Leary's embedding of ⟨F, t | [t, r], r ∈ R⟩
    into a group of type FP_2).
- Leary, *Subgroups of almost finitely presented groups*, Math. Ann. 372 (2018), arXiv:1610.05813:
  "every countable group embeds in a group of type FP_2".
- Higman, *Subgroups of finitely presented groups*, Proc. Roy. Soc. London Ser. A 262 (1961).
  The graph imports it through `mikaelian-explicit-higman-embedding`.
- No later answer was found. The literature check was bounded: arXiv abstract pages and HTML fetched by
  hand, and the web-search budget of this session ran out after two searches.

## 2. Graph map (landed c034abacc6, e7d92b58d4 and the splitting landing)

- Root with three answer routes: `zaremsky-1-01-by-yes` (Part 2 yes), `zaremsky-1-01-by-no` (Part 1 no,
  the obstruction lane's claim) and `zaremsky-1-01-by-mixed`.
- Answer claims:
  - `every-type-fn-group-embeds-in-a-type-fn-plus-1-group`
  - `every-finitely-presented-group-embeds-in-an-f-infinity-group`
  - `some-type-fn-group-embeds-in-no-type-fn-plus-1-group` (lane z1-01-embed-neg)
  - `some-finitely-presented-group-embeds-in-no-f-infinity-group`
- Homological equivalents, with routes both ways through Theorem A and Higman:
  - `universal-fp-group-embeds-in-rp-fp-infinity-group` (lane z1-01-ffz-fpinf, 807c320863). It replaced
    this lane's equivalent claim over all f.g. recursively presented groups, landed at e7d92b58d4 and
    retired together with its two routes. The attempts from §4 and §6 were merged into it.
  - `every-fg-rp-group-has-rp-fp-n-hosts-for-each-finite-n`
  - Host fence: `universal-fp-group-hosts-have-unsolvable-word-problem`.
- Dead routes into the affirmative first part:
  - `type-fn-hosts-via-higman-rope-trick`, killed by Theorem B;
  - `type-fn-hosts-via-vertex-groups-over-fp-edges`, killed by
    `fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups`.

## 3. Universal forms (proved in the root body)

Let U be a universal finitely presented group and E_m = "every finitely presented group embeds in a group of
type F_m".
- E_m ⟺ U has an F_m host ⟺ every f.g. recursively presented group has a recursively presented FP_m host.
- Part 2 = E_∞. Part 1 ⟺ E_m for all finite m ≥ 3.
- Only one input matters, and a host of U has these features: infinite cohomological dimension
  (Thompson's F ≤ U), torsion of every order, unsolvable word problem, and it is not simple (finitely
  presented simple groups have solvable word problem, and F_m hosts are finitely presented for m ≥ 2).

## 4. Defect criterion for HNN hosts (standard; a node can be written from this section)

Let H = HNN(V, L', α, β) be finitely generated and X = ∏_Λ ZH (a right module).
- Bieri–Eckmann: H is of type FP_n iff H_k(H; X) = 0 for 1 ≤ k ≤ n−1 and every Λ. At k = n the comparison
  target is 0, and H_0 is fine since H is finitely generated.
- Bass–Serre: 0 → ZH ⊗_{ZL'} Z → ZH ⊗_{ZV} Z → Z → 0 gives the Mayer–Vietoris sequence
  … → H_k(L'; X) --φ_k--> H_k(V; X) → H_k(H; X) → H_{k−1}(L'; X) --φ_{k−1}--> H_{k−1}(V; X) → …
- So H is of type FP_n iff φ_k is onto for 1 ≤ k ≤ n−1 and one-to-one for 0 ≤ k ≤ n−2.
- For K ≤ H the groups H_k(K; X) are the defects of K: X is a product of free ZK-modules, and they vanish
  in positive degrees when K is of type FP_∞.
- A rope is an HNN host whose edge and vertex defects cancel through φ. Leary's rope cancels in degree 1.
  Theorem B says the classical rope's edge group has an infinite-dimensional H_2 that no vertex term absorbs.

## 5. Why the known machines do not raise finiteness

- Splittings over FP_{n+1} edge groups: vertex groups inherit FP_{n+1} (landed node, complete proof).
- Twisted Brin–Thompson groups SV_G: the criteria put G itself in the hypothesis (type [A_n] asks G of
  type F_n, FFWZ arXiv:2603.24687v2, Definition 1.3). Their vertex stabilizers in the Stein–Farley-type
  complexes contain wreath-type copies of G.
- Röver–Nekrashevych and cloning-system groups: the stabilizers again contain the input.
- Ascending HNN telescopes: a finitely generated subgroup of the kernel of E → Z lies in a copy of the base,
  so they convert hosts (Theorem A) but do not create them.
- Brown's criterion: the input must meet stabilizers of type FP_∞ or act freely. Any cocompact construction
  in which G fixes a vertex needs G of type F_{n+1}.

## 6. Product ropes: preliminary computation (UNREVIEWED)

Setting: V = P × G with P of type FP_∞, α = (ι, 1) and β = (ι, π) for an embedding ι: L' → P and a
homomorphism π: L' → G.
- X restricted to V is a product of free ZV-modules. P is FP_∞, so Tor^{ZP}_q(X, Z) = 0 for q ≥ 1, and the
  Lyndon–Hochschild–Serre spectral sequence gives H_k(V; X) ≅ H_k(G; X_P) with X_P = X ⊗_{ZP} Z, again a
  product of free ZG-modules.
- α(L') ≤ P × 1, and H_k(P; X) = 0 for k ≥ 1, so α_* = 0 in positive degrees. Then φ_k = −t_* β_*.
- β_* composed with the edge isomorphism factors through H_k(L'; X) → H_k(π(L'); X_N) → H_k(G; X_P), where
  N = ker π acts on X through ι(N) ≤ P. The collapse X_N → X_P is onto; its kernel carries products over
  the cosets ι(N)\P.
- Level-3 requirements: β_* one-to-one and onto in degree 1, onto in degree 2, and φ_0 one-to-one.
- Guess, not proved: with both P and N of type FP_∞ and G not of type FP_2, degree-1 injectivity fails,
  because the kernel of X_N → X_P contributes G-defects. If so, a higher rope needs P or N outside FP_∞ with
  defects arranged degree by degree. That is the structure a positive answer must supply.

## 7. Next targets

1. Write the defect criterion of §4 as a node with a proof route.
2. Decide the guess in §6. A proof makes it an established obstruction with `invalidates:` on a
   product-rope route. A counterexample gives the first candidate higher rope.
3. Search for hosts of the universal group where the input acts freely on a highly connected complex with
   FP_∞ stabilizers: Thompson-like groups built over infinite-cd, torsion-rich FP_∞ groups with a
   non-stabilizer embedding.
