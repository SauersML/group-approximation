---
rg: 2
id: lifted-thompson-t-perfect-centre-cubically-elliptic
kind: claim
title: "The lift T-bar of Thompson's T is perfect and has no proper finite-index subgroup; so its central translation z is elliptic in every commensurating action (every CAT(0) cube complex, every discrete wall space) of every group containing T-bar, and no cubical construction proves lifted-thompson-t-is-a-t-menable"
distinct_from:
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that makes fibre elements of nV elliptic in commensurating actions of nV; this makes the centre of the subgroup T-bar elliptic in commensurating actions of T-bar itself, which need not extend to nV
  commensurating-loxodromics-split-their-centralizers: that is the general lemma; this verifies its hypotheses for T-bar (perfectness, via elements of T with rotation number 1/n) and draws the consequence for lifted-thompson-t-is-a-t-menable
  lifted-thompson-t-center-has-relative-t: that is relative (T) of (T-bar, <z>) against all Hilbert-space cocycles; this is only its commensurating (cubical) shadow
---

**ESTABLISHED** by `lifted-thompson-t-perfect-centre-cubically-elliptic-proof`.

**Setting.** `T̄` is the group of homeomorphisms of `R` lifting elements of Thompson's `T`
(acting on `S^1 = R/Z`), and `z(x) = x + 1` generates its centre `⟨z⟩ = ker(T̄ → T)`.

**Statement.**
1. For every `n ≥ 1` there is `ĝ ∈ T̄` with `ĝ^n = z`.
2. `T̄ = [T̄, T̄]`, so `Hom(T̄, R) = 0`.
3. `T̄` has no proper subgroup of finite index.
4. In every action of any group `G ⊇ T̄` on a set `X` with a commensurated subset `A`, the wall
   count `ℓ(z^N) = |z^N A Δ A|` is bounded in `N`. In particular `z` has a bounded orbit in every
   action of `T̄` on a CAT(0) cube complex (any dimension), and every cnd function of the form
   `ℓ` (discrete walls) on `T̄` is bounded on `⟨z⟩`.

**Consequence.** By `haagerup-splits-as-coset-plus-subgroup-properness`, a proof of
`lifted-thompson-t-is-a-t-menable` needs a cnd function proper on `⟨z⟩`. By item 4 it cannot come
from a commensurating action, of `T̄` or of any overgroup such as `C(C,Z) ⋊ T` or `2V`. This
closes the question "cubical approaches are not excluded" left open in the 2026-09-18 w8 attempt
on `lifted-thompson-t-is-a-t-menable`, negatively for cubical methods. It also settles the
rational-Euler-class worry recorded there: a homomorphism `T̄ → R` nonzero on `z` does not exist.

**Literature.** Item 2 agrees with Maruyama, arXiv:2002.12743, §2.1 (verbatim from the
extracted text): "Since ~T = [ ~T, ~T ] and the defect of rotation number is equal to 1, we have
scl( ~T ) = Q≥0." The proof here is self-contained and does not use that source.

**Novelty.** Items 1-3 are standard (Ghys-Sergiescu). Item 4 is a direct application of
`commensurating-loxodromics-split-their-centralizers`. Not independently reviewed.
