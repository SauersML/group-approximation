---
rg: 2
id: extension-decoders-are-locally-balanced
kind: claim
title: Decoders with a translation lift or a quantum extension are locally balanced, and locally balanced automata are post-surjective and measure preserving
distinct_from:
  window-balance-is-a-fiber-upper-bound: that characterizes preservation of the uniform measure by fibre counts averaged over all contexts; this asks the fibre count to be balanced inside every single context, which is strictly stronger and forces post-surjectivity.
  absorptions-give-post-surjective-strict-pairs: that proves absorption decoders are post-surjective from the homeomorphism Psi; this isolates the local counting invariant behind that, and proves it also for every decoder whose pullback extends to a quantum automaton, monomial or not.
  strict-automata-yield-strict-quantum-endomorphisms: that proves a decoder with a quantum extension preserves the uniform measure (condition D1 there); this proves such a decoder is locally balanced, hence post-surjective, so the decoder-extension form of that hole implies strict-pairs-admit-post-surjective-decoders.
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that turns a post-surjective decoder into a dual failure; this supplies post-surjective decoders from extension data.
---

**ESTABLISHED (elementary)** by [[extension-decoders-are-locally-balanced-proof]].

**Setting.** `G` is a group and `A` a finite alphabet with `q = |A| >= 2`. A cellular automaton `sigma` on `A^G`
has a finite memory `W` containing `e`: `sigma(u)_h` is determined by `u` on `hW`. For a finite set `E`, a
pattern `p` on `E` and a *context* `c` on `G \ E`, write `p ∪ c` for the joined configuration. `mu` is the
uniform product measure.

**Definition (locally balanced).** Let `S` be a finite set containing `e`. For each finite `F ⊆ G` put

    D_F = F ∪ F S W^-1,      B_F = D_F \ F .

For a context `c` on `G \ FS` and `v` a pattern on `D_F`, let

    N_c(v) = #{ p ∈ A^(FS) : sigma(p ∪ c) agrees with v on D_F } .

Off `D_F` the output `sigma(p ∪ c)` does not depend on `p`. Call `sigma` *locally balanced with lift set `S`*
if, for every finite `F` and every context `c`, `N_c(v)` depends only on `v|_(B_F)`. Equivalently: within every
context, the output on `F` is uniformly distributed given the output on the collar `B_F`. The definition uses
no algebraic structure on `A`.

**Theorem.**

1. **(A) Translation lifts give balance.** Let `A = Z/d` and let `sigma` have a translation lift in the sense
   of (3) of `monomial-quantum-automata-are-topological-bernoulli-absorptions`. If `S ∋ e` contains every
   coordinate that `T_e` can change, then `sigma` is locally balanced with lift set `S`. In particular the
   first coordinate `sigma = pr_1 Psi` of every topological Bernoulli absorption is locally balanced.
2. **(B) Quantum extensions give balance.** Let `A = Z/d`, and let `Phi` be a quantum automaton on
   `(x)_G M_d` (shift-equivariant, unital *-endomorphism, with `Phi(M_d at e)` inside the local algebra of a
   finite set `R ∋ e`) such that `Phi(f) = f o sigma` for every `f ∈ C(A^G)`. Then `sigma` is locally balanced
   with lift set `R`. Neither strictness nor monomiality of `Phi` is used.
3. **(C) Reversible automata are balanced.** If `sigma` is bijective and `sigma^-1` has memory `W'`, then
   `sigma` is locally balanced with lift set `{e} ∪ W'^-1`.
4. **(D) Balance gives post-surjectivity and measure preservation.** Let `sigma` be locally balanced with lift
   set `S`.
   - *(D1) Strong post-surjectivity with lifts inside `ES`.* If `z` agrees with `sigma(u)` off a finite set
     `E`, then some `u'` agrees with `u` off `ES` and has `sigma(u') = z`.
   - *(D2) Measure preservation.* `sigma_* mu = mu`.
5. **(E) One-site lifts always exist.** Let `A = Z/d` and let `sigma` be locally balanced with lift set `S`.
   Then there is a local bijection `T_e` of `A^G` with the following properties:
   - it changes only coordinates in `S`;
   - `T_e^d = id`;
   - `sigma o T_e = sigma + delta_e`.

   Setting `T_g = lambda_g T_e lambda_g^-1` gives every other condition of a translation lift except
   `T_e T_g = T_g T_e`. That condition only needs checking for `g` in a finite set determined by `S` and `W`.

**Consequences.**

- **No dual surjunctivity.** A locally balanced `sigma` that is not injective is post-surjective by (D1). It
  is therefore not pre-injective, since post-surjective and pre-injective automata are reversible
  (Capobianco–Kari–Taati, `capobianco-kari-taati-dual-surjunctivity-toolkit`). So the group is not dual
  surjunctive.
- **Sofic calibration.** On sofic groups, post-surjective implies pre-injective (CKT). So there, locally
  balanced is the same as reversible, by (C) and (D1).
- **Strictly stronger than measure preservation.** On `Z` over `Z/2`, `sigma(u)_n = u_n + u_(n+1)` preserves
  `mu`. It is not post-surjective, because it is pre-injective and not injective. So by (D1) it is not locally
  balanced for any lift set. The pointwise-context count is the real necessary condition. Its average over
  contexts is condition (D1) of `strict-automata-yield-strict-quantum-endomorphisms` and
  `window-balance-is-a-fiber-upper-bound`.
- **The decoder-extension form of the quantum transfer implies the post-surjective-decoder hole.**
  - Suppose some decoder `sigma` of a strict pair has a quantum extension. Then by (B) and (D1) `sigma` is a
    post-surjective decoder of that strict pair.
  - So every proof of `strict-automata-yield-strict-quantum-endomorphisms` that extends a decoder pullback also
    proves `strict-pairs-admit-post-surjective-decoders` for that group. It then also refutes dual
    surjunctivity there, by `post-surjective-decoders-convert-strict-pairs-to-dual-failures`.
  - Such a proof must solve the free choice of the decoder rule at infinite defect chains, where that hole sits.
    Choosing a decoder only for measure preservation cannot suffice.
- **Where translation lifts can fail.** By (E), for a locally balanced decoder the only obstruction to a
  translation lift, and hence by the monomial theorem to an absorption, is the commutation of one-site lifts
  with their translates. This is recorded as `locally-balanced-decoders-admit-translation-lifts`.
