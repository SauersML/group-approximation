---
rg: 2
id: shannon-window-fakes-transfer-to-canonical-hosts
kind: claim
title: Minimal-window Shannon fakes pull back along window-injective homomorphisms, and no torsion-free group realizes the incidence pattern of any of the 151 known fakes
distinct_from:
  torsion-free-windows-have-minimal-shannon-certificates: that conjectures LP >= 1 in torsion-free groups; this proves the LP is smallest on the canonical host of the incidence pattern, gives the exact refutation criterion (a fake anywhere whose host is torsion-free), and shows that every known fake fails that criterion because its pattern forces torsion.
  minimal-window-shannon-derivations-miss-rokhlin-domination: that exhibits the torsion fakes; this moves fakes between hosts and shows that none of them can reach a torsion-free group with its pattern intact.
  shannon-window-fakes-on-klein-and-infinite-dihedral-hosts: that extends the fakes to order-2 and order-7 hosts; this certifies that the patterns of those fakes, and of 147 more, force an element of finite order in every realization.
  bernoulli-rokhlin-deficit-has-a-finitary-witness: that passes true Rokhlin deficits along canonical hosts; this passes values of the Shannon LP relaxation, where the host minimises the LP, and adds the torsion census.
  rokhlin-maximality-closed-under-local-embeddings: that closes true Rokhlin maximality under local embeddings; this concerns the minimal-window Shannon LP and when its fakes can reach torsion-free groups.
artifacts:
  - research/artifacts/shannon-fakes-canonical-host-transfer-2026-09-17.md
  - experiments/shannon-canonical-hosts-2026-09-17/host_tietze.py
  - experiments/shannon-canonical-hosts-2026-09-17/fake_hosts_scan.py
  - experiments/shannon-canonical-hosts-2026-09-17/random_fake_hosts.py
  - experiments/shannon-canonical-hosts-2026-09-17/recheck_forced_torsion.py
  - experiments/shannon-canonical-hosts-2026-09-17/recheck_all.txt
  - experiments/shannon-canonical-hosts-2026-09-17/base_rate.py
  - experiments/shannon-canonical-hosts-2026-09-17/base_rate.txt
  - experiments/shannon-canonical-hosts-2026-09-17/free_host_lp.py
  - experiments/shannon-canonical-hosts-2026-09-17/free_host_lp.txt
  - experiments/shannon-canonical-hosts-2026-09-17/onerel_hosts_z6.py
  - experiments/shannon-canonical-hosts-2026-09-17/onerel_hosts_z6.txt
---
**ESTABLISHED** by `shannon-window-fake-transfer-by-pullback-and-tietze-census`.

**Setup.** `LP_G(E,F)` is the minimal-window Shannon LP of
`research/artifacts/shannon-window-certificates-2026-09-17.md`, Section 2. It minimises
`h(y_f0) + h(x_1 y_F) - h(y_F)` over polymatroids on `{x_g : g in FE ∪ {1}} ∪ {y_f : f in F}`, subject to:
- independent unit `x`;
- `y_f` a function of `x_(fE)`;
- translation invariance inside the window.

The **incidence pattern** `P` of `(E,F)` is the index sets `E`, `F`, the coincidences `fe = f'e'` and the products
`fe = 1`. The **canonical host** `H_P` has one letter per element of `E` and `F`, with relators `f e (f'e')^-1` and
`f e` for these coincidences and products.

**Claim.**

1. **Transfer.** Let `pi : H -> G` be a homomorphism that is injective on `F_H E_H ∪ {1}` and on `F_H`. Then
   `LP_H(E_H, F_H) <= LP_G(pi E_H, pi F_H)`. In particular `LP_{H_P} <= LP_K` for every group `K` realizing `P`.
2. **Refutation criterion.** A configuration with `LP < 1`, in any group, whose canonical host `H_P` is
   torsion-free refutes `torsion-free-windows-have-minimal-shannon-certificates`.
3. **Census.** Take each of the 151 configurations with numerical `LP < 1` listed in
   `experiments/shannon-canonical-hosts-2026-09-17/recheck_all.txt`. These include every exact fake of
   `minimal-window-shannon-derivations-miss-rokhlin-domination` and of
   `shannon-window-fakes-on-klein-and-infinite-dihedral-hosts`. For each one, `H_P` has, after Tietze moves, a
   relator `u^k` with `k >= 2`. Here `u` is:
   - a window point `f e` with `fe != 1`;
   - a reader ratio `f f'^-1` or `f^-1 f'`; or
   - an offset ratio `e e'^-1` or `e^-1 e'`.

   So `u` is a nontrivial element of finite order in every realization, and the pattern is realized in **no**
   torsion-free group. For example, the `Z/3` fake `E = {0,1,2}`, `F = {0,1}` has
   `H_P = <e0, e2 | (e0^-1 e2)^3>`.

**Class killed.** Every attempt to refute the torsion-free claim by carrying a known fake to a torsion-free group
with its pattern intact fails. This covers lifts to free or surface groups, torsion-free covers and subgroups,
torsion-free quotients, and embeddings into universal torsion-free groups. By item 1, carrying a fake means
realizing its pattern. By item 3, every such attempt dies at the realization step, on the named relator `u^k`.

**Supporting computation (not part of the established statement).** `base_rate.txt` and `free_host_lp.txt` cover
all 1274 configurations of the exhaustive scans of `Z/3`, `Z/4`, `Z/5`, `Z/6`, `(Z/2)^2` and `S_3`, with
`|E| <= 4`, `|F| <= 3` and ground set at most 10. Each pattern either:
- forces torsion (551 patterns, containing all 115 fakes of these scans); or
- has a free canonical host on which the LP solver returns value `>= 1` (723 patterns).

Numerically, `fake-incidence-patterns-force-torsion` holds on every one of these patterns.

## Attempts
