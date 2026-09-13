---
rg: 2
id: spin-m-trapping-string-factorization-proof
kind: route
title: BString -> BSpin_m is an infinite loop map over BO, so MSpin_m is an MString-algebra and smashing with MSpin_m factors through MString
target: spin-m-trapping-factors-through-string-bordism
requires: []
---

**(a) The ring map.** Connective real K-theory ko has Omega^∞ ko ≃ BO x Z,
with the infinite loop structure coming from Whitney sum. Its connective
covers give BSpin = Omega^∞ tau_{>=4} ko and BString = Omega^∞ tau_{>=8} ko.
The Postnikov map k: tau_{>=4} ko -> Sigma^4 HZ is an isomorphism on pi_4.
BSpin is 3-connected, so H^4(BSpin; Z) ≅ Hom(pi_4 BSpin, Z), and Omega^∞ k
represents a generator of H^4(BSpin; Z). That generator is ±lambda. So
lambda is an infinite loop map, and so is lambda mod m, the composite with
Sigma^4 HZ -> Sigma^4 HZ/m. Taking fibres of spectra,

    tau_{>=8} ko = fib(k)  ->  fib(tau_{>=4} ko -> Sigma^4 HZ/m) =: bspin_m,

and Omega^∞ bspin_m ≃ BSpin_m. The map of fibres commutes with the maps to
tau_{>=4} ko, hence to BO. Thom spectra of infinite loop maps to BO are
E_∞ ring spectra, and maps of infinite loop spaces over BO give E_∞ ring
maps (May–Quinn–Ray; Ando–Blumberg–Gepner–Hopkins–Rezk). This gives
MString -> MSpin_m.

**(b) Base change.** MSpin_m is an MString-module through (a). For every
spectrum X there is an equivalence, natural in X,

    MSpin_m ∧ X ≃ MSpin_m ∧_{MString} (MString ∧ X).

Under it MSpin_m ∧ f corresponds to MSpin_m ∧_{MString} (MString ∧ f).
The MString-module map MString ∧ f: MString ∧ A -> MString ∧ B is the free
extension of the spectrum map A -> B -> MString ∧ B. If that composite is
null, the extension is null, and so is its base change. □

**(c) Seeds.** Put g' = (g_{c−1}, ..., g_1, h): M -> G^c and let
q: G^c -> G^{∧c} be the quotient. The map c_c: G^c -> G is 1 on the fat
wedge, so f = cbar_c o q o g'. The Spin_m-structure on M gives a class
[M] in MSpin_m_{dim M}(M), and f_*[M] − (const)_*[M] is the reduced part of
f_*[M]. That reduced part equals (cbar_c)_* applied to the reduced part of
(q o g')_*[M], because (cbar_c)_* is induced by a based map. By (b),
MSpin_m ∧ s_c is null, so (cbar_c)_* vanishes on reduced MSpin_m-homology.
Hence [M, f]_red = 0. Proposition 7.1 of
`research/artifacts/class-four-lambda-mod-eight-trapping-part3-2026-09-13.md`
evaluates the trapped class of (f o pr_M) (+) 1_Q as
±<c_r(Q)^N, [X]>·[M, f]_red, which is 0. □

**(d)** is the contrapositive of (c) with c = 5. □

*Remarks.* (i) Nothing here uses a splitting of MString. The known
2-local splittings (ko-modules for MSpin) are not available, and tmf
detects nu, epsilon, kappa and kappa-bar. So (d) does not by itself kill
class five. (ii) The implication runs one way. MSpin_m is not an
MString-module retract, so a string-visible commutator need not be
Spin_m-visible.
