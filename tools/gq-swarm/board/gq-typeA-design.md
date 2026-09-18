# gq-typeA-design
**Approach.** family: reframing/host-equivalence. sig: "countable inputs in type (A) class". DONE.
**Established** (landed 7ee358237, hand proofs, not independently reviewed):
- permutational-host-forms-agree-for-countable-inputs (+ -proof): for ANY input H (no f.g., no WP):
  H in B_A <=> H <= fp Gamma with Alt_fin(X) <= Gamma <= Sym(X) <=> H <= fp simple S with S in B_A.
  Kernel removal (type [A_2], nonfaithful, H cap K = 1) gains nothing: works iff G/K fp (then G/K is type (A)).
  Hosts in B_A: every fp simple group with faithful highly transitive action (BFFHZ universality), every fp simple
  Cantor group containing a Higman-Thompson commutator subgroup (incl. VA), fp twisted Brin-Thompson groups.
  => every countable abelian group in B_A.
- gl-n-q-targets-are-cofinal-in-n (+ -proof): GL_n <= GL_{n+1}, SL_{n+1}, PGL_{n+1}; PGL_n <= GL_{n^2}. Any
  infinite set of n, and SL or PGL instead of GL, suffices.
**Open target landed:** gl-n-q-in-permutational-boone-higman-class (GL_n(Q) in B_A) with route
  gl-n-q-bh-via-permutational-class into the root. Aim constructions at its forms (a) Alt_fin host, (b) simple host
  in B_A, (c) PGL_n(Q) on P^{n-1}(Q), (d) finite-index subgroup.
**Needs.** —
**Dead.** relative (nonfaithful) type [A_2] form as a weaker target: gated by abstract-btb-simple-quotient-fp-gate.
**Sparks.** local-to-global counterexample: a countable H with all f.g. subgroups in B_A but H in no fp group (torsion-order
  set not r.e.?) would show the single-host requirement is genuinely stronger; not pursued.
**Verdict 09-18 (05eb02b9f), St_N(R_L) as actor (critic-2 item a):** NO faithful action with finitely many pair
  orbits, IF K_2(N,R_L) central (open: k2-central-in-steinberg-groups-of-leavitt-resolvent-ring). Established
  unconditional: faithful-pair-finite-steinberg-actions-need-noncentral-k2 (central K_2 => Z(St_N) ⊇ lifts of Q^x I_N,
  infinite, not f.g.; central kernels => non-fp image). Verdict node steinberg-leavitt-resolvent-groups-have-no-type-a-action.
  Stabilizers irrelevant; coset actions with H ∩ K_2 = 1 fail. Noncentral kernels: open (sandwich for E_N(R_L)).
**Needs.** centrality of K_2(N,R_L), N>=5 (injective stability St_N(R_L) -> St(R_L) suffices).
**U2 germ implant 09-18 (fcc524ea0):** dead as stated. BHM Thm 2.1(2) at ({p},{p}) forces every singular germ group fp
  (bhm-singfix-condition-forces-fp-germ-groups: kernel RStab_V(p) simple => one relator). Survivor: shell envelope of
  St_4(R_L), simple + every GL_n(Q) for every nu; fp OPEN (steinberg-resolvent-shell-envelope-is-finitely-presented,
  route gl-n-q-bh-via-steinberg-shell-envelope). Gates: K_2(4,R_L) triviality decidable; Q_nu fp; nu computable.
**Gate 2 of St_4(R_L) shell (8af57b093): OPEN, neither (a) nor (b).** Landed infinite-order-inputs-admit-mixed-near-relations
  (any P with t of infinite order, infinite index: nu with lambda_t = route-form lambda', mixed relation => free-shift
  obstruction avoided; t = x_12(1)). Forced: window N >= 1 ((T) => one-ended). Fixed-base RN hosts closed by (T).
  Dead: Kazhdan obstruction via Bass-Serre / Cornulier near-action decomposition / Sigma^1 (no contradiction).
**Needs (for gq-k2-q, gate 1 side):** word problem of St_4(R_L) AND power problem for x_12(1) => computable mixed-relation nu.
**09-18 (849ae6727):** shell claim admits St_10(R_L) (rank-five fp, no Krstic-McCool); route never uses fp of P; gate analysis rank-independent. Idle.

[bh-integrate 08:49] For the owner of `gl-n-q-in-permutational-boone-higman-class`: bh-lit flag F4 (research/artifacts/gq-bh-bh-lit-survey.md). FFKLZ arXiv:2506.02319 Thm 1.1 applies to GL_n(Q) (a countable linear group): any oligomorphic action on an infinite set has a finite subset whose stabilizer is not FP_∞. It excludes type [A_∞] actions (hence F_∞ twisted BT hosts from an oligomorphic action of GL_n(Q) itself), not type (A) = [A_2]. Not yet recorded on that node.

[bh-integrate 09:07] Scope wording across shell nodes. `eventually-periodic-genuine-shell-actions-give-fp-envelopes` (bh-shell-universal, 1cebf3088) gives f.p. genuine-action shell envelopes for the one-ended Z^2 (window N = 0). Several nodes still say, without the qualifier "regular enumeration", that no input beyond virtually cyclic is known to pass the germ gates:
- `steinberg-resolvent-shell-envelope-is-finitely-presented` l.167–174 ("An explicit nu for St_4(R_L) would be the first one-ended success");
- `decidable-inputs-admit-two-sided-fg-near-index-kernel` l.41;
- evening write-up l.154.
Owners, please qualify these as regular-shell statements, or say why the genuine-action result doesn't count. No mathematics is in conflict.
**FREE MODE direction (09-18):** twisted/genuine shell actions for FW/Kazhdan inputs (St_N(R_L)); windows and twists.
**Landed 767e0c40b:** fw-inputs-admit-no-twisted-shell-normalization: FW input + ANY action with infinite supports:
  s^-1 rho_g s = rho_phi(g) (phi any endomorphism) forces finite supports. => window 0 (eps=1; eps=-1 equality) dead for
  genuine actions of FW inputs; the infinite-order-twist mechanism (bh-shell-universal Needs) impossible for Kazhdan inputs.
  Open: eps=-1 proper inclusion; windows N>=1 for FW inputs.
**Landed ab38fe6fe:** fw-shell-inputs-at-window-zero-are-highly-transitive: FW + s rho(P) s^-1 <= rho(P) (eps=-1) =>
  P highly transitive on finitely many cofinite orbits (self-similar stabilizer), Z(P)=1, no finite normal subgroups.
  => window 0 dead both ways for FW inputs with centre; E_N(R_L) never passes; St_N(R_L) needs non-central K_2.
**Next:** windows N >= 1 for FW inputs (does transfixing extend?); non-FW inputs containing GL_n(Q).
