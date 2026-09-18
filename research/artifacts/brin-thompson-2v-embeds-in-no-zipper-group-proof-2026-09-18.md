# A zipper action is a commensurating action proper modulo the trivial subgroup, so it captures no distorted element; restrict to the Callard--Salo element

*Attempt artifact (2026-09-18), formerly route `brin-thompson-2v-embeds-in-no-zipper-group-proof` into `brin-thompson-2v-embeds-in-no-zipper-group`, requires [cubical-coset-proper-actions-capture-distorted-elements, brin-thompson-mv-contains-a-distortion-element, sft-topological-full-groups-have-the-haagerup-property]. Demoted from the graph at landing because the swarm-0917 referee stage returned no votes for this established result (votes lost), so it has not survived review. Restore it as a route once a full referee pass survives.*

## Sources (read from the arXiv source tex, 2026-09-17)

- **Hughes**, *Local similarities and the Haagerup property*, arXiv:0804.0610, with the
  appendix by D. Farley (file `LocSimHaag_plus_appendix.tex`).
  - Definition 5.1, l.690–704: "A discrete group $\Gamma$ has a zipper action if there is a
    left action $\Gamma\curvearrowright\mathcal E$ of $\Gamma$ on a set $\mathcal E$ and a
    subset $Z\subseteq\mathcal E$ such that (1) for every $g\in\Gamma$, the symmetric
    difference $gZ \,\triangle\, Z$ is finite, and (2) for every $r>0$,
    $\{ g\in\Gamma ~|~ |gZ\,\triangle\, Z|\leq r\}$ is finite."
  - Theorem ZipperExistence, l.804–809: "If $\Gamma$ is a locally finitely determined group
    of local similarities on a compact ultrametric space $X$, then $\Gamma$ has a zipper
    action."
  - Appendix, l.1124: "A discrete group $\Gamma$ has a zipper action if and only if $\Gamma$
    acts properly on a space with walls."
- **Matui**, *Topological full groups of one-sided shifts of finite type*, arXiv:1210.5800
  (file `tfgossftarXiv.tex`).
  - Definition `zipper`, l.2080–2088, is Hughes's definition, cited as "[Defintion 5.1]".
  - Theorem, l.2110: "The action $\phi:[[G]]\curvearrowright\Omega$ is a zipper action."
    Here `G` is the étale groupoid of a one-sided irreducible SFT, the setting of
    `sft-topological-full-groups-have-the-haagerup-property`.
  - Proof, l.2134–2143 (the step quoted in the target): "Then
    $\phi_\alpha([C_\lambda])=[WC_\lambda]$ is in $Z$ if and only if there exists $i$ such
    that $C_\lambda$ is contained in $C_{\nu_i}$. […] Therefore
    $\#(Z\setminus\phi_\alpha^{-1}(Z))=\#(\phi_\alpha(Z)\setminus Z)$ does not exceed the
    number of admissible words of length less than $m(\alpha)$, and hence is finite."
- **Callard–Salo**, arXiv:2208.00685, l.330–334: "By~\cite[Theorem~1.5]{Ha21}, a group with
  distortion elements does not admit such an action, thus: […] The Brin-Thompson group $mV$
  does not act properly on a CAT$(0)$ cube complex for $m \geq 2$." The distortion element
  itself is imported through `brin-thompson-mv-contains-a-distortion-element`.

## Proof

**Step 1 (restriction).** Let `G ↷ E` with `Z ⊆ E` be a zipper action and let `L ≤ G`. The
restricted action `L ↷ E` with the same `Z` is a zipper action. Condition (1) holds
elementwise. The set in condition (2) for `L` is the intersection of `L` with the finite set
for `G`.

**Step 2 (item 1 of the Theorem).** Let `ℓ(g) = |gZ △ Z|`.
- Condition (1) says `Z` is commensurated, which is the setting of
  `cubical-coset-proper-actions-capture-distorted-elements` with `X = E` and `A = Z`.
- Condition (2) says each sublevel set `{ℓ ≤ R}` is finite, that is, it lies in finitely
  many left cosets of `H = {1}`. So `ℓ` is proper modulo the trivial subgroup.
- Let `f ∈ G` have infinite order and be distorted in a finitely generated `L ≤ G`.
  - Item 2 (capture) of that claim gives `f^d ∈ {1}` for some `d ≥ 1`, which contradicts
    infinite order.
  - Directly: by Step 0 of its route, `ℓ(f^N) ≤ K|f^N|_L = o(N)`.
  - By item 1 (bounded-or-linear), `ℓ(f^N) ≤ C` for all `N ≥ 0`.
  - The powers `f^N` are pairwise distinct, so `{ℓ ≤ C}` is infinite, which contradicts
    condition (2).
- Hence `f` is undistorted. This proves item 1.

**Step 3 (item 2).** Fix `m ≥ 2`.
- By `brin-thompson-mv-contains-a-distortion-element`, there are a finitely generated
  `L ≤ mV` and `f ∈ L` of infinite order with `|f^N|_L = O(log^4 N)`.
- Suppose `φ: mV → G` is injective and `G` has a zipper action.
  - `φ(L)` is finitely generated, with generating set the image of that of `L`.
  - `φ` restricts to an isomorphism `L → φ(L)` carrying word lengths to word lengths, so
    `|φ(f)^N|_{φ(L)} = |f^N|_L`.
  - `φ(f)` has infinite order.
  - So `φ(f)` is a distorted element of `G`, which contradicts Step 2.
- The three host classes listed in the target have zipper actions:
  - SFT full groups, by Matui l.2110;
  - locally finitely determined groups of local similarities, by Hughes, Theorem
    ZipperExistence;
  - groups acting properly on a space with walls, by the appendix, l.1124.

So `mV` embeds in none of them. ∎

**Remarks.**
- The Matui import is used only through the statement at l.2110, which is exactly "[[G]] has
  a zipper action". The listing in `sft-topological-full-groups-have-the-haagerup-property`
  identifies the class of groupoids `G` it covers. No Haagerup-to-finiteness import is
  used anywhere.
- Step 3 needs only `m = 2`, because `2V ≤ mV`. The target's statement for all `m ≥ 2` is
  the Callard–Salo theorem for every `m`, as imported.
