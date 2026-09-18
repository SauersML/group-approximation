# bh-finf-hyp
Direction (09-18): the F_∞ half of Zaremsky's QI question (arXiv:2201.00711, l.495–497) for EVERY hyperbolic group, beyond the cubulated case (2V).
**Landed 62622d30a:** `bbmz-host-finiteness-reduces-to-the-vertex-boundary-groupoid` (ESTABLISHED lane proof) plus Attempt 7 on `hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups`.
- The free factor Z is inert. Every element of [[G*Z|∂_h]] is finitary off finitely many coset pieces Y_v ≅ ∂_h G, and H_k(groupoid) = H_k(G; C(∂_h G)) for k ≥ 2.
- Necessary test (Li): D(host) F_n ⇒ dim_Q H_k(G; C(∂_h G, Q)) < ∞ for 2 ≤ k ≤ n. It passes for surface groups and in top degree for PD(n). OPEN in middle degrees.
- Finite germ theory (BHM 2407.03149) fails on both resolutions: ∂_h pieces are chopped by V; point pieces (the Bowditch / stabilizer engine) have a transport base that is not finitely generated.
**Not achieved:** an F_∞ host for Kazhdan hyperbolic groups.
**Landed (2):** `horofunction-boundary-homology-reduces-to-the-branch-locus`: descent spectral sequence over the branch locus; dim B ≥ m−1 for S^m; the Sp(n,1) test is (4n−2)-dimensional tiling cohomology, expected to pass. No MSI job was run: no usable Sp(n,1) data exists and no bounded computation can certify the answer.
**Landed (3) af235c6d8:** `horofunction-atom-configurations-have-finitely-many-types` (finite configuration types; finite-type coding of fiber products) and `finite-germ-extensions-with-singular-blocks-are-f-n` (the block BHM theorem; full groups with V have no blocks; the coset transport base is not finitely generated, so germ-local methods over coset loci are dead).
**Landed (4):** `hyperbolic-cone-matching-holds-off-the-branch-locus`. Cone matching holds off the branch locus. The nucleus-tile operad has (VE) and finite transformations. Square filling ⇐ (C), no cycle in the non-surjective nucleus automaton, which is decidable. Under (C) the type is finite, so (G) is not needed.
**Landed (5) 22fc66382:** the cone-matching test (one Slurm job, 19 s). Calibration passes; the grid control fails at corners; the pentagon group has 4 persistent failure chains per generator (wall endpoints), so (C) fails. Colour-tameness holds iff every colour has an operation with inputs of that colour only; this holds after Cuntz stabilization.
**Next:** the configuration-matching test (unions of the paired atoms at wall endpoints), one more job. If it holds, use configuration tiles; if it fails, a Thumann operad on atom shadows is dead.
Status: this pass done.
