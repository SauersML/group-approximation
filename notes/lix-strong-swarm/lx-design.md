# lx-design — odd-primary operations design (LIX strongest swarm, 2026-09-12)

Owns `notes/lix-strong-swarm/design-*.md`, `notes/lix-strong-swarm/tools/design_*`.  No Lean, no clone.

## GREEN (design deliverables)
* `notes/lix-strong-swarm/design-oddp.md`: the end-to-end lemma list for the reduced powers at an odd
  prime (operations, top power, descent constant, D-form Cartan comparison, the total operation
  `P_tot`, vanishing V, normalisation `μ = −1`, and the narrowed consumer interface with landed
  spellings).
* Findings sent to lanes (SendMessage): lx-cartan-b (confirmed V route, no riffle on Φ_A, odd-odd
  redundant after V, `P_tot` primary and no V′), lx-pzero (general `P⁰ = id` unproducible, narrowing, μ via
  `T²`, normalisation with `κ = 1`, `mul_single` for the torus), lx-splitK / lx-torusP / lx-slice2
  (narrowed fields), lx-toppower (top power route; `c₁` only for μ), lx-redpow (`oddDClass` at every j),
  lx-bundleP (`m = 1`), lx-review (audit list).
* Model tests: `notes/lix-strong-swarm/tools/design_oddp_modeltest.py` (MSI acn112, python3.11): `checks=10237 fails=0`
  (constants c_1, c_2 = −1, c_{2k} = (−1)^k, Wilson, riffle sign; A_r θ_r-semilinear chain map with augmentations
  r^k / r^{k+1} under the tree's altCoeff; σ_r T = T^r σ_r; surviving Cartan pairs under V, control: p pairs without V).

## AUTHORED, UNVERIFIED
* none (no Lean).

## NEEDS
* lx-cartan-b: (K) D-form comparison at every j; (V) at least on degree-2 classes; the `T²` corner sign
  `(−1)^m`.
* lx-toppower: (A) top power; (C) `c₁ = m!` class level.
* lx-pzero: link line bundle on `T²` with `e(L) ≠ 0` (Step C over K) for `μ = −1`.

## TRAPS
* `msi "cat > remote"` < local file can upload an EMPTY file with exit 0 (first model-test run printed only
  the sentinel).  Upload with `rsync -e "ssh -S /tmp/msi-login.sock -o HostKeyAlias=login.msi.umn.edu"`.
* A graded Cartan formula on arbitrary even classes needs V′ (`[D_a x] = 0` for `a > d(p−1)`); do not state
  one.  Use `P_tot` (multiplicative with no vanishing lemma) and read graded components only on junk-free
  classes.
* `P⁰ = id` holds on 1 and on Euler classes of line bundles; an arbitrary mod-`p` degree-2 class need not
  reduce an integral class, so no `ℂP^M` universal example covers it.
