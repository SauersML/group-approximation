---
rg: 2
id: contracting-rsgs-have-fp-full-closures-proof
kind: route
title: Local agreement with G makes every local action of the full closure at long enough words a local action of G
target: contracting-rsgs-have-fp-full-closures
requires:
  - contracting-rsgs-embed-in-fp-simple-groups
---

**Item 1.** Let `h ∈ [[G]]`. By compactness of `E` there is a finite partition of `E` into
cones `C_{α_1}, …, C_{α_r}` and elements `g_1, …, g_r ∈ G` with `h = g_i` on `C_{α_i}`.
- For every path `β` extending `α_i`, the local action `h|_β` equals `g_i|_β`, since both are
  read off from `h = g_i` on `C_β ⊆ C_{α_i}` by the defining identity `f(β·ω) = f̄(β)·f|_β(ω)`.
- Every path of length at least `max |α_i|` extends some `α_i`. So all but finitely many
  local actions of `h` are local actions of the `g_i`. Each `g_i` has finitely many local
  actions, so `h` has finitely many: `h` is rational, and `[[G]] ≤ R_{Γ,E}`.
- A local action of `h` occurring at infinitely many `β` occurs at infinitely many `β`
  extending a single `α_i`, so it lies in `N_{g_i}`. Hence `N_h ⊆ N_G`, and `N_{[[G]]} ⊆ N_G`.
  The reverse inclusion holds because `G ≤ [[G]]`.
- `[[G]]` contains `G`, so it realizes every canonical similarity between cones that `G`
  realizes. It is an RSG, and it is full because `[[[[G]]]] = [[G]]`.

**Item 2.** Contracting means `Σ_Γ` has an irreducible core (a property of `Γ`, unchanged)
and `N_G` is finite. By item 1 `N_{[[G]]} = N_G`, so `[[G]]` is a full contracting RSG. BBMZ
Theorem B and Proposition `contr_to_simple` (`contracting-rsgs-embed-in-fp-simple-groups`,
items 4 and 5) then apply to `[[G]]`.
