---
rg: 2
id: master-route-needs-only-topological-freeness
kind: claim
title: Both master routes use freeness of the subshift only as topological freeness, plus torsion-free isotropy for the K-gate, so the crux object is a rigid minimal topologically free SFT
distinct_from:
  cantor-crossed-hosts-are-closed-under-boundary-products: that already allows non-free actions for torsion-free Farrell-Jones hosts (valid hosts); this treats the master route, where the acting group contains the input and may have torsion.
  free-group-boundary-shifts-are-quantum-rigid: that supplies a rigid minimal topologically free SFT over F_m x F_n and raises the question; this answers which route steps survive the loss of freeness.
---

**ESTABLISHED** (lane bh-g3-topfree, 2026-09-18; elementary audit of established nodes, not
reviewed; no priority claimed).

## Setting

`Λ` is a finitely generated group, `A` a finite alphabet, `X ⊆ A^Λ` a nonempty subshift. The action is:
- **minimal**;
- **topologically free**: for every `g ≠ 1` the fixed set `Fix(g)` has empty interior;
- where stated, with **torsion-free isotropy**: no nontrivial element of finite order fixes a point.
  Equivalently every finite subgroup acts freely.

Topological freeness implies faithfulness (if `g` acted trivially, `Fix(g) = X` would be open and
nonempty). If `Λ` is infinite then `X` is a Cantor space. Indeed, if `X` were finite then points
would be open, so topological freeness would make the action free and `|Λ| <= |X|`. And an isolated
point would make its orbit open, so by minimality `X` would be one orbit of isolated points, hence
finite.

## Claim

**(1) Ring route** `boone-higman-via-leavitt-units-of-rigid-sft-overgroups`, with `B = LC(X, F_2) ⋊ Λ`
and `L = L_(F_2)(1,2)`:

| step | what it uses | needs freeness? |
|---|---|---|
| fp crossed product (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`) | `Λ` fp, `X` a quantum rigid SFT | no; that node assumes no freeness, minimality or amenability |
| 2. central simplicity (`free-minimal-cantor-crossed-products-are-central-simple`) | minimal and topologically free | no; that node is stated for topological freeness |
| 3. `Λ -> B^x -> (B ⊗ L)^x` injective | the `u_λ` are a free `LC(X,F_2)`-basis, `X ≠ ∅` | no |
| 4. `K_1 = K_2 = 0` for `B ⊗ L` | see below | only torsion-free isotropy |
| 5. Khanh transfer (`leavitt-tensor-hosts-acyclic-steinberg-and-fp`) | `B` simple unital fp, `K_1 = K_2 = 0` | no dynamics |
| 6. unit-group simplicity (`central-simple-leavitt-tensor-unit-groups-are-simple`) | `B` central simple, `K_1 = K_2 = 0` | no dynamics |

Step 4:
- If `Λ` is torsion-free Farrell–Jones, `cantor-crossed-product-leavitt-tensors-are-k-trivial` gives
  `K_* = 0` for **every** action.
- If `Λ` is Farrell–Jones with torsion, `farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`
  needs exactly that finite subgroups act freely, i.e. torsion-free isotropy.
- For general `Λ` with torsion-free isotropy, `free-crossed-leavitt-k-gate-is-a-farrell-jones-instance`
  (whose setting is exactly "finite subgroups act freely") makes the gate equivalent to one
  Farrell–Jones instance.
- Torsion in isotropy must be excluded: the trace detector gives `K_1 ≠ 0` for `Z/2` acting trivially
  (`leavitt-tensor-k1-sees-traces-of-nilpotent-matrices`).

So the premise pair (E), (K) of that route may be replaced by (E′) =
`decidable-groups-lie-in-fp-topologically-free-crossed-products` and (K′) =
`torsion-free-isotropy-leavitt-tensor-hosts-have-trivial-k1-k2`. The route with these premises is
`boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts`.

**(2) Group route** `boone-higman-via-v-times-aperiodic-sft-full-groups`:
- Its step 1 ("`X` is Cantor") holds by the Setting paragraph.
- Its step 3 ("`T` effective") uses only that `Λ ⋉ X` is effective. For a group action this is exactly
  topological freeness, since an open set of isotropy arrows over an open `U` means some `g ≠ 1` fixes
  a nonempty open subset of `U`.
- Its step 4 (minimality) is unchanged.
- Its step 5 (`Λ ↪ F(T)`) needs faithfulness.
- Steps 6–7 are groupoid-general.

So the implication (P1) ∧ (P2) ⇒ BH holds with "free" replaced by "topologically free" in both
premises. Whether (P2), or the necessity theorem `fp-v-times-subshift-full-groups-force-quantum-rigidity`
(stated for free actions), survives the relaxation is not claimed.

**(3) The relaxation is strict.**
- **Free groups count.** `F_n` (n ≥ 2) carries no free SFT at all, recalled from Piantadosi as used in
  `deterministic-time-lifts-inherit-quantum-rigidity`. It also carries no strongly aperiodic SFT, since
  it has at least two ends (Cohen, recalled). Yet it carries the quantum rigid, minimal, topologically
  free end shift (`free-group-boundary-shifts-are-quantum-rigid`), with torsion-free isotropy
  (point stabilizers are trivial or infinite cyclic). So the one-endedness requirement of the free
  version disappears.
- **Virtually cyclic groups still fail.** Suppose `Z ≤ Λ` has finite index. Restricting to `Z` recodes
  `X` as a nonempty `Z`-SFT, which contains a `Z`-periodic point. Its `Λ`-orbit is finite, so a minimal
  `X` is finite, and then topological freeness forces `Λ` finite.

**(4) Scaffold.** `Λ = F_m × F_n` with `X = ∂T_m ⊠ ∂T_n` satisfies every non-input hypothesis of (1):
- it is quantum rigid, minimal and topologically free (`free-group-boundary-shifts-are-quantum-rigid`
  with `quantum-rigidity-is-product-stable`);
- `Λ` is torsion-free and CAT(0), hence Farrell–Jones (Bartels–Lück and Wegner, recalled).

So `(B ⊗ L)^x` is finitely presented (conditional on Khanh) and simple. This is not a new host: by
`boundary-crossed-product-is-a-leavitt-path-algebra`, `B ≅ L_k(E_m) ⊗ L_k(E_n)`, a tensor of Leavitt
path algebras. The pair is already a valid host in the sense of the node
`cantor-crossed-hosts-are-closed-under-boundary-products`, and its word problem lies in a fixed class.
It certifies only that the relaxed route has no obstruction outside its input-dependent premises.

## Where a decidable input can enter

- **Track A (`G ≤ Λ`).** (E′) over an fp overgroup `Λ_0 ≥ G`. Free factors add nothing for the input.
  By `quantum-rigidity-is-product-stable`, and since the product action of `Λ_0 × F_n` on
  `X_0 × ∂T_n` is minimal (respectively topologically free) iff the `Λ_0`-factor is,
  `X_0 ⊠ X_∂` has each of the three properties iff `X_0` does. What is new is that compression-type
  (boundary) codings now count as candidates for `X_0`, not only strongly aperiodic ones.
- **Track B (fixed `Λ`, input in units).** Unchanged. The scaffold's language is fixed, so gate U
  (`translation-like-inputs-embed-in-full-groups-over-a-fixed-group`) still needs input-programmed
  decorations. Deterministic decorations keep rigidity (`deterministic-extensions-of-rigid-sfts-are-rigid`)
  and topological freeness, but they are not by themselves a source of programmed language.
- **Isotropy.** The relaxation allows infinite cyclic isotropy. The input never needs to sit in
  isotropy, since it embeds through `Λ ↪ B^x` in any case.

## Lesson for general BH

The master route never needed a free action: it needs an effective (topologically free) minimal
action, plus freeness of finite subgroups for the K-gate. So the crux object is (★′), a quantum-rigid
minimal topologically free SFT with torsion-free isotropy over an fp overgroup of the input. That
admits the compression mechanism of boundary shifts, which is available exactly over non-amenable
groups where free SFTs are scarce. Decidability is still consumed at this gate, by
`rigid-topologically-free-sfts-force-solvable-word-problem`.
