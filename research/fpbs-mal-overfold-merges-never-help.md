---
rg: 2
id: fpbs-mal-overfold-merges-never-help
kind: claim
title: On every finite F(a,b)-set, merges of the folded L_{j+1}-graph outside the kernel of its map onto the folded L_j-graph never lower the least number of merges that collapse that kernel, so deep_j(Q) = law_j(Q) = r(Q^(j))
distinct_from:
  fpbs-mal-depth-promotion-equals-overfold-merge-number: that proves Q_j(X) = inf_m deep_j(Q_m)/|Q_m| and deep_j <= law_j = r(Q^(j)); this is the open reverse inequality deep_j >= law_j, which that node does not decide.
  fpbs-word-chords-are-dominated-by-merges: that shows arcs with arbitrary labels are dominated by vertex merges of one folded graph; this asks that merges which are not in the kernel be dominated by merges that are, a different exchange.
  fpbs-mal-bernoulli-single-stage-floor: that is the Bernoulli floor; this is one of the two finite inputs of the route fpbs-mal-depth-floor-from-overfold-domination to it.
  fpbs-mal-twisted-level-seed-density-uniform-witness: that is the other input, a uniform lower bound on r(Q_m^(j))/|Q_m|; this is the exchange statement that turns lawful seeds into all seeds.
artifacts:
  - research/artifacts/fpbs-overfold-level0-projection-2026-09-19.md
  - experiments/fpbs-overfold-projection-2026-09-17/oprime.py
  - experiments/fpbs-overfold-projection-2026-09-17/oprime_climb.py
  - experiments/fpbs-overfold-projection-2026-09-17/single_seed.py
  - experiments/fpbs-overfold-projection-2026-09-17/climb_j2_n7_k6.txt
  - experiments/fpbs-overfold-projection-2026-09-17/single_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_search.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n4_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n5_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n6_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n8_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n4_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n5_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/seedtypes.py
  - experiments/fpbs-depth-overfolding-2026-09-17/pair_automaton.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange_n40_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange_sanov29_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange_n20_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/compare.py
  - experiments/fpbs-depth-overfolding-2026-09-17/compare_n30_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/compare_n20_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/compare_n12_j3.txt
  - research/artifacts/fpbs-overfold-intransitive-levels-2026-09-19.md
  - experiments/fpbs-overfold-sharing-2026-09-17/intransitive_exact.py
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n5_j1.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n8_j1.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n6_j1_3orb.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n4_j2.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n5_j2.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exhaustive.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exh_n6_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exh_n5_j2.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/pairtrees.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/multiorbit.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exact_multi.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/localsearch.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/local_cayley24_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/top_vs_law.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/top_vs_law_n6_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exact_multi_s3_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exh_n3_j3.txt
  - research/artifacts/fpbs-overfold-free-fold-2026-09-19.md
  - experiments/fpbs-overfold-free-fold-2026-09-17/freefold.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/bfs_free.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/check_law0.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/law_census.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/census_d6.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/all_single.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/as_j1_d5.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/as_j1_d6.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/as_j2_d4.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/single_stats.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/stats_j1_d5.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/stats_j2_d4.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/stats_j3_d2.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/level2.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/l2_j1_d4.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/l2_j1_d6.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/retract_test.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/rt_j1_d3.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/rt_j2_d2.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/check_nonsplit.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/check_nonsplit.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/rank_states.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/rank_states_j1_d3.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/matching.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/matching_j1_d4.txt
  - research/artifacts/fpbs-overfold-exact-c-census-2026-09-19.md
  - experiments/fpbs-overfold-exact-c-2026-09-17/deep.c
  - experiments/fpbs-overfold-exact-c-2026-09-17/export.py
  - experiments/fpbs-overfold-exact-c-2026-09-17/check_auts.py
  - experiments/fpbs-overfold-exact-c-2026-09-17/census.py
  - experiments/fpbs-overfold-exact-c-2026-09-17/run12_j1_cap5.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/run24a_cap4.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/run24b_cap4.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/census_cayley24_j1_cap3.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/census_cayley24_j1_law5_cap4.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/census_cayley24_j2_cap3.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/run20e_cap4.txt
  - research/artifacts/fpbs-overfold-depth-shift-reduction-2026-09-19.md
  - experiments/fpbs-overfold-breaker-2026-09-17/pb.py
  - experiments/fpbs-overfold-breaker-2026-09-17/smallk.py
  - experiments/fpbs-overfold-breaker-2026-09-17/reduction_check.py
  - experiments/fpbs-overfold-breaker-2026-09-17/principal_types.py
  - experiments/fpbs-overfold-breaker-2026-09-17/principal_types_j4.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/doublecoset_check.py
  - experiments/fpbs-overfold-breaker-2026-09-17/doublecoset_j4.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j1_n7.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j2_n6.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j3_n4.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j4_n3.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j1_n14.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j2_n9.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j3_n8_single.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j4_n5_single.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/redcheck_j2_i1_n5.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/redcheck_j3_i1_n3.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/redcheck_j3_i2_n3.txt
  - research/artifacts/fpbs-overfold-cascade-2026-09-19.md
  - experiments/fpbs-overfold-cascade-2026-09-17/export_model.py
  - experiments/fpbs-overfold-cascade-2026-09-17/model_j1.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/model_j2.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/cascade.c
  - experiments/fpbs-overfold-cascade-2026-09-17/run_all.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_law.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_over.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_all.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n5000_j2_law.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n5000_j2_over.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n5000_j2_all.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/greedy_n1000_j1_all.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/greedy_n1000_j1_law.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc.py
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc_mixed_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc_small_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/ostep.py
  - experiments/fpbs-overfold-cascade-2026-09-17/ostep_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_lev0.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/run_oloc.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/run_oloc_mixed.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/run_oloc_small.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/run_ostep.sh
  - research/artifacts/fpbs-overfold-other-chains-2026-09-19.md
  - experiments/fpbs-overfold-other-chains-2026-09-17/chains.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/randchains.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/run_rand.sh
  - experiments/fpbs-overfold-other-chains-2026-09-17/rand_r3_n1.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/run_named.sh
  - experiments/fpbs-overfold-other-chains-2026-09-17/named_n5.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/named_n6.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/run_named2.sh
  - experiments/fpbs-overfold-other-chains-2026-09-17/named_n5b.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/rank3_family.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/rank3_family.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/rank3_malnormal.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/rank3_malnormal.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/rank3_random.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/rank3_random.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/malnormal.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/malpair.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/run_malpair.sh
  - experiments/fpbs-overfold-other-chains-2026-09-17/malpair.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/verify_gaps.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/malpair_verify.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/run_malpair2.sh
  - experiments/fpbs-overfold-other-chains-2026-09-17/malpair2.txt
  - experiments/fpbs-overfold-other-chains-2026-09-17/ri_test.py
  - experiments/fpbs-overfold-other-chains-2026-09-17/run_ri.sh
  - experiments/fpbs-overfold-other-chains-2026-09-17/ri_test.txt
  - research/artifacts/fpbs-doublecoset-transport-all-depths-2026-09-19.md
  - experiments/fpbs-doublecoset-transport-2026-09-17/transport.py
  - experiments/fpbs-doublecoset-transport-2026-09-17/transport_j9.txt
  - experiments/fpbs-doublecoset-transport-2026-09-17/doublecoset_j6.txt
  - research/artifacts/fpbs-overfold-rank2-relative-inertia-2026-09-19.md
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/stall.py
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/cover.py
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/maln.py
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/searchA.py
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/searchB.py
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/searchC.py
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/searchD.py
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/selftest.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/searchA_L1_ml7.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/rank3_ml6.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/random_r2.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/random_r3.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/nonmal_r2_S3.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/mal_r2_S3.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/mal_r2_A4.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/mal_r3_S3.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/chain_ml6.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/needC_j1_S3.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/needC_j1_A4.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/needC_j2_S3.txt
  - experiments/fpbs-overfold-nonabelian-ri-2026-09-17/searchD_nx6.txt
  - research/artifacts/fpbs-overfold-cap5-2026-09-19.md
  - experiments/fpbs-overfold-cap5-2026-09-17/deep5.c
  - experiments/fpbs-overfold-cap5-2026-09-17/deep5fp.c
  - experiments/fpbs-overfold-cap5-2026-09-17/beam.c
  - experiments/fpbs-overfold-cap5-2026-09-17/lcheck.c
  - experiments/fpbs-overfold-cap5-2026-09-17/ostep_verify.py
  - experiments/fpbs-overfold-cap5-2026-09-17/repcheck.py
  - experiments/fpbs-overfold-cap5-2026-09-17/sweep_wide.py
  - experiments/fpbs-overfold-cap5-2026-09-17/inst12j2_law8.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/inst12j2_law6a.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/inst12j2_law6b.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/validate_inst12_cap4.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/validate_inst12_law.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/validate_fp_inst12_cap4.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/validate_fp_inst12_law.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/law_j2.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/sweep_wide_B1000.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/force_j2law8_r2.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/force_j2law8_r3.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/force_j2law6a_r1.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/force_j2law6b_r1.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/wit_j2law8_force_r1.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/wit_j2law8_force_r2.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/wit_j2law8_force_r3.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/lcheck_j2law8_force_r1.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/lcheck_j2law8_force_r2.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/lcheck_j2law8_force_r3.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/ostep_verify_j2law8.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/climb_j2law8.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/pairs_j2law8.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/pairs_j2law6a.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/pairs_j2law6b.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/triples_j2law8.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/triples_j2law6a.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/triples_j2law6b.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/run24a_cap5_oomkilled.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/run24a_cap5_deep5_stopped.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/run24a_cap5.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/run24b_cap5.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/run24b_fullkey_level4.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/inst12j1_law8.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/law12j1_law8.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/run12j1law8_cap6.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/run12j1law8_fullkey_level5.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/beam12j1law8_B20000_r1.txt
  - experiments/fpbs-overfold-cap5-2026-09-17/beam12j1law8_B1e6_r2.txt
  - research/artifacts/fpbs-overfold-one-pair-joins-2026-09-19.md
  - experiments/fpbs-overfold-one-pair-2026-09-17/folding.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/test_lemma1.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/test_lemma1.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/expansion.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/expansion_check.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/monphi_k1.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/run_s2_g5_l8.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/run_s3_g3_l10.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/run_s4_g6_l5.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/witness.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/witness_W.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/ri_k1.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/ri_j1_s11.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/ri_j2_s13.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/selftest_ri.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/selftest_ri.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/transfer.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/transfer2.py
  - research/artifacts/fpbs-overfold-spectral-percolation-2026-09-19.md
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/hyper.py
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/spectral.py
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/spectral_out.txt
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/balls.py
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/balls_out.txt
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/tree_count.py
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/tree_count_out.txt
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/weighted_lp.py
  - experiments/fpbs-overfold-spectral-percolation-2026-09-17/weighted_lp_j1_r3.txt
  - research/artifacts/fpbs-overfold-malnormal-host-census-2026-09-20.md
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/census.py
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze.py
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze2.py
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_w19.py
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_viol.py
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/k1_L1_s13.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/k1_rand_s11.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/k1_L1overL2_s14.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/k1_nonmal_s12.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/k2_L1overL2_s21.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_L1_s33.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_L1overL2_s31.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_rand_s35.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_nonmal_s12.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_w19.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_viol.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_L1overL2_2_s34.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze_rand2_s32.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze2_L1overL2_s41.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze2_rand_s42.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze2_nonmal_s43.txt
  - experiments/fpbs-overfold-malnormal-host-census-2026-09-17/analyze2_L1_3_s44.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/eb_family.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/family_d4_d10.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/cayley_blocks.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym4_j2_b2.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym4_j2_b3.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym4_j2_b4.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym5_j3_b2.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/spectral_sym_m3_m8.txt
  - research/artifacts/fpbs-overfold-free-factor-shn-2026-09-20.md
  - experiments/fpbs-overfold-image-claim-2026-09-17/ab_split.py
  - experiments/fpbs-overfold-image-claim-2026-09-17/dichotomy.py
  - experiments/fpbs-overfold-image-claim-2026-09-17/mix_check.py
  - experiments/fpbs-overfold-image-claim-2026-09-17/surj_check.py
  - experiments/fpbs-overfold-image-claim-2026-09-17/a_refute.py
  - experiments/fpbs-overfold-image-claim-2026-09-17/kern.py
  - experiments/fpbs-overfold-image-claim-2026-09-17/kviol_check.py
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/ab_r2_m1_sub.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/ab_r3_m1_sub.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/dich_mal2_sub_k1.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/dich_mal2_sub_k2.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/dich_mal3_sub_k1.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/dich_L1overL2_fi_k2.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/kern_mal3_s21.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/kern_nonmal2_s33_small.txt
  - experiments/fpbs-overfold-image-claim-2026-09-17/out/kern_mal2_s32_small.txt
  - research/artifacts/fpbs-overfold-midn-exact-2026-09-20.md
  - experiments/fpbs-overfold-midn-2026-09-17/rel.c
  - experiments/fpbs-overfold-midn-2026-09-17/midn.py
  - experiments/fpbs-overfold-midn-2026-09-17/struct_midn.py
  - experiments/fpbs-overfold-midn-2026-09-17/anneal.c
  - experiments/fpbs-overfold-midn-2026-09-17/run_law8.sh
  - experiments/fpbs-overfold-midn-2026-09-17/run_queue.sh
  - experiments/fpbs-overfold-midn-2026-09-17/inst12j1_law8.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_p0.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_p1.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_p2.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_p3.txt
  - experiments/fpbs-overfold-midn-2026-09-17/run_law8_s5.sh
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_q0.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_q1.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_q2.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_q4.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_q5.txt
  - experiments/fpbs-overfold-midn-2026-09-17/law8_s5_q6.txt
  - experiments/fpbs-overfold-midn-2026-09-17/rand_j1_n20.txt
  - experiments/fpbs-overfold-midn-2026-09-17/rand_j1_n30.txt
  - experiments/fpbs-overfold-midn-2026-09-17/rand_j2_n12.txt
  - experiments/fpbs-overfold-midn-2026-09-17/psl23_j1_law5.txt
  - experiments/fpbs-overfold-midn-2026-09-17/psl23_j1_law6_s3.txt
  - research/artifacts/fpbs-overfold-sym-covers-2026-09-20.md
  - experiments/fpbs-overfold-sym-covers-2026-09-17/covers.py
  - experiments/fpbs-overfold-sym-covers-2026-09-17/rel.c
  - experiments/fpbs-overfold-sym-covers-2026-09-17/all_j1_k2_s3.txt
  - experiments/fpbs-overfold-sym-covers-2026-09-17/lawge5_j1_k2_s4.txt
  - experiments/fpbs-overfold-sym-covers-2026-09-17/run_law6.sh
  - experiments/fpbs-overfold-sym-covers-2026-09-17/law6_0_s5.txt
  - experiments/fpbs-overfold-sym-covers-2026-09-17/law6_1_s5.txt
  - experiments/fpbs-overfold-sym-covers-2026-09-17/law6_2_s5.txt
  - experiments/fpbs-overfold-sym-covers-2026-09-17/law6_3_s5.txt
---

**OPEN.** Notation is as in
[[fpbs-mal-depth-promotion-equals-overfold-merge-number]]. Here `Q` is a
finite `L`-set, `m : Γ_{j+1}(Q) → Γ_j(Q)` is the canonical surjection, and:
- `deep_j(Q)` is the least number of same-fibre pairs of `Γ_{j+1}(Q)` whose
  fold-closure contains `ker(m)`;
- `law_j(Q)` is the same least number, over pairs inside `ker(m)`.

Prove that for every finite `Q` and every `j ≥ 0`,

```text
deep_j(Q)  =  law_j(Q)   ( = r(Q^{(j)}) ).
```

A weaker statement suffices for the floor: `deep_j(Q) ≥ c · law_j(Q)`, with
`c > 0` independent of `j` and `Q`.

**Why it matters.**
- With [[fpbs-mal-depth-promotion-equals-overfold-merge-number]], this gives
  `Q_j(X) = Q_j^law(X)` on every essentially free profinite `X`. That is:
  - labels outside `L_j` never help promote `E_{L_{j+1}}` to `E_{L_j}`;
  - the promotion problem at depth `j` is the depth-0 problem of the
    twisted levels `Q_m^{(j)}`.
- This is statement (U) of the w14 D1 setup, on profinite witnesses, with
  `c = 1`.

**Known.**
- `j = 0`: `Γ_0(Q)` is the Schreier graph, so every same-fibre pair lies in
  `ker(m)`. Equality is trivial.
- `deep_j ≤ law_j` always.

**Evidence (computations).**
- **Exact values.** `exact_search.py` computes both numbers exactly by
  breadth-first search over the distinct partitions reached by `k` seeds.
  - It covers 70 random transitive levels: `j = 1` with `n = 4, 5, 6, 8`,
    and `j = 2` with `n = 4, 5`.
  - The graphs `Γ_{j+1}(Q)` have up to 100 vertices.
  - In all 70 cases, `deep_j = law_j`.
  - The files `exact_n5_j1.txt`, `exact_n8_j1.txt` and `exact_n5_j2.txt`
    were made before a fix to partition deduplication. The fix only speeds
    the search up, and the values found are still exact.
- **Exchange.** `exchange.py` takes random inclusion-minimal promoting seed
  sets of mixed types. It tries to swap each overfold seed for a single
  lawful seed.
  - At `j = 1`: 0 failures among 208 overfold seeds on random `n = 40`
    levels, and 0 among 80 on the Sanov line `P^1(F_29)`.
  - At `j = 2`: 12 of 135 single swaps fail. These are on non-minimum sets,
    so a proof cannot be a naive one-for-one local exchange.
  - No short word `w` gives a uniform exchange rule `y ↦ y·w` per seed type.
- **Heuristic search.** `compare.py` runs greedy search with restarts over
  all seed types. It never found fewer seeds than the exact `law_j`:
  - `j = 1`, `n = 30`: 8 levels;
  - `j = 2`, `n = 20`: 8 levels;
  - `j = 3`, `n = 12`: 5 levels.
- **Structure.** Over the finite core of `L_{j+1}` (one point), the lawful
  pairs form a single component of the pair graph. The overfold pairs form
  11, 87 and 559 components for `j = 1, 2, 3` (`seedtypes.py`,
  `pair_automaton.py`). So overfold seed types multiply quickly, but no
  computed instance uses one profitably.

**What a proof must use.** For a general pair of subgroups in place of
`L_{j+1} ≤ L_j`, the analogous exchange has no reason to hold. Its
generating-set analogue fails: a subgroup of a 2-generated finite group can
need 3 generators. So a proof has to use features special to this chain,
such as rank 2 and the single lawful component above.

## Attempts

- **Cross-orbit sharing on `L_j`-intransitive levels** (swarm-0917-w16-w16-fp-break,
  belief breaker, 2026-09-19). No counterexample found.
  - *Idea.* `law_j` is additive over `L_j`-orbits. A single overfold pair
    whose ends map to different `L_j`-orbits could serve two orbit kernels,
    giving `deep < law`. The earlier 70 levels were almost all
    `L_j`-transitive, so they never tested this.
  - *Computation.* `intransitive_exact.py` computes `law_j` and `deep_j`
    exactly on 53 `L`-transitive levels with at least 2 `L_j`-orbits:
    - `j = 1`: `n = 5`, `n = 8`, and `n = 6` with 3 orbits;
    - `j = 2`: `n = 4, 5`.
  - *Result.* `deep_j = law_j` in all 53. In 17 of them the minimum witness
    contains overfold seeds, but never with fewer seeds. The script counts
    overfold seeds; it does not separate the cross-orbit ones.
  - *Proved on the way (Lemma A of the artifact).* Every promoting seed set
    has at least `sum_O (s_O - 1)` seeds, where `s_O` is the number of
    `L_{j+1}`-orbits in the `L_j`-orbit `O`. This holds with or without
    cross-orbit seeds.
    - So cross-orbit seeds cannot save on connectivity. Any sharing would
      have to come from fold-closure identifications.
    - The bound has density 0 on free towers, so it is not a floor.
  - *Where it dies.* The sharing mechanism is never observed. The open case
    is still large transitive levels, beyond exact search.
  - Details: `research/artifacts/fpbs-overfold-intransitive-levels-2026-09-19.md`.
- **2026-09-19, swarm-0917-w16-w16-fp-last1 (census-computation +
  reframing): OPEN; no counterexample; exact reformulation.** Scripts and
  outputs are in `experiments/fpbs-overfold-relative-rank-2026-09-17/`.
  - **Pullback form (proved here).** Let `R` be the rose on `a, b`, `C_j`
    the Stallings core of `L_j`, and `ι : C_{j+1} → C_j` the immersion
    induced by `L_{j+1} ≤ L_j`. Then:
    - `Γ_{j+1}(Q) = Q ×_R C_{j+1}`, with `m = id × ι` and the over map
      equal to the first projection.
    - Proof: the fold of the generator paths maps onto this pullback, which
      is folded. The map is injective: if `p·u = p'·u'` and `u, u'` end at
      the same core vertex, then `r = u u'^{-1} ∈ L_{j+1}` is readable from
      `p` and ends at `p'`. So `r u'` is readable from `p`, and it reduces to
      `u`. By determinism, both endpoints coincide.
    - So a same-fibre pair is `(q; c, c')` with `c, c' ∈ V(C_{j+1})`, and it
      is lawful iff `ι c = ι c'`.
    - A fold closure is the least family `(E_q)_{q∈Q}` of equivalence
      relations on `V(C_{j+1})` that contains the seeds and satisfies:
      `c E_q c'` and `x` readable at both imply `cx E_{qx} c'x`.
  - **Seed types are finite trees.** A seed type is an off-diagonal
    component of the pair graph `C_{j+1} ×_R C_{j+1}`.
    - The type of `(c, c')` corresponds to the double coset
      `L_{j+1} u_c u_{c'}^{-1} L_{j+1}`. Its `π_1` is
      `L_{j+1} ∩ g L_{j+1} g^{-1}`, which is trivial by malnormality.
    - `pairtrees.py` checks that every component is a tree, for
      `j = 0..3`. The counts of ordered components are 2, 24, 176 and 1120.
      Of these, exactly 2 are lawful, which is one unordered type. The
      remaining 11, 87 and 559 unordered types are overfold.
    - Consequence: one seed yields a fixed finite set of `|T_i|`
      identifications, whatever `Q` is. Every dependence of the closure on
      `Q` comes from transitivity inside fibres.
  - **Relative-rank form (proved here, `Q` transitive under `L_{j+1}`).**
    Fix a base point `p` and set:
    - `S = Stab_L(p)`, `K = S ∩ L_{j+1}` and `K' = S ∩ L_j`;
    - `D_law` for the lawful double coset of `L_{j+1}` (it lies in `L_j`);
    - `D_1, …, D_r` for the overfold double cosets (they lie in
      `L ∖ L_j`).

    A seed at the vertices reached by words `u` and `u'` contributes the
    loop `g = u u'^{-1}` to `π_1`. Then:
    - the seed is same-fibre iff `g ∈ S`, and lawful iff `g ∈ K'`;
    - every `g ∈ S ∩ D_i` is realised by some seed;
    - the closure contains `ker(m)` iff `⟨K, g_1, …, g_k⟩ ⊇ K'`. This holds
      because vertices reached by `w` and `w'` coincide in a folded graph
      iff `w w'^{-1} ∈ π_1`.

    Hence:

    ```text
    deep_j(Q) = min{ k : g_i ∈ S ∩ (D_law ∪ D_1 ∪ … ∪ D_r), ⟨K, g⟩ ⊇ K' }
    law_j(Q)  = min{ k : g_i ∈ K' ∩ D_law,                   ⟨K, g⟩ = K'  }
    ```

    Any witness `H = ⟨K, g⟩` satisfies `H ∩ L_j = K'` and
    `H ∩ L_{j+1} = K`. So (O) says exactly this: elements of the overfold
    double cosets, which lie outside `L_j`, never generate `K'` over `K`
    more cheaply than elements of `D_law`. This is a relative-rank statement
    for the malnormal chain `L_{j+1} < L_j < L`.
  - **Exhaustive census.** `exhaustive.py` covers every transitive `L`-set
    of size `n`, up to isomorphism (7, 26, 97 and 624 classes for
    `n = 3, 4, 5, 6`, the counts in OEIS A057005).
    - `law_j` is computed exactly, as a sum over the components of
      `Γ_j(Q)`.
    - `deep_j < law_j` is then ruled out by exact breadth-first search over
      all same-fibre seeds, up to level `law_j − 1`.
    - Results: `deep_j = law_j` in every class, with no flags:
      - `j = 1`, `n ≤ 6`: law values 1–4; 624 classes at `n = 6`, 92 of
        them not `L_1`-transitive;
      - `j = 2`, `n ≤ 5`: 24 of 97 classes at `n = 5` are not
        `L_2`-transitive;
      - `j = 3`, `n = 3`.
    - Classes that are not `L_j`-transitive are new ground. Only there can a
      seed join two components of `Γ_j(Q)` (a cross-orbit seed), and the
      random census never produced such a `Q`.
  - **Structured levels (heuristic).** These are the Cayley actions of every
    2-generated subgroup of `S_3`, `S_4` and `S_5` of order at most 24.
    - `localsearch.py` does 10 restarts of 300 swap steps each, over all
      seed types, with `k = law − 1` seeds.
    - It found no witness to `deep < law` on 54 levels at `j = 1`
      (`local_cayley24_j1.txt`).
    - These levels include law values up to 12, and levels with up to 6
      `L_1`-orbits, where cross-orbit seeds are plentiful.
    - The exact search `exact_multi.py` gives these values
      (`exact_multi_s3_j1.txt`):
      - `S_3` with 3 orbits: `law = 3` and `deep = 3`;
      - an order-12 group with 3 orbits: `law = 6` and `deep ≥ 4`.
  - **Top family is not a shortcut.** Let `full_j` be the least number of
    seeds that collapses every fibre onto `Q`, so that `deep_j ≤ full_j`.
    - On 15 random levels with `n = 6` and `j = 1`, `full_1 > law_1` holds
      exactly in 14 of them (`top_vs_law_n6_j1.txt`). The 15th has
      `law_1 = 3` and `full_1 ≥ 3`.
    - So a counterexample, if one exists, sits at an intermediate closed
      family.
  - **Cheap bound (proved).** Let `N` be the number of components of
    `Γ_j(Q)` with nontrivial kernel. Folding never leaves a connected
    component, and one seed touches at most two components. Hence
    `deep_j(Q) ≥ ⌈N/2⌉`, whereas `law_j(Q) ≥ N`.
  - **Remaining gap.** Two things are still missing:
    - a proof of the relative-rank statement above, or its weak form with a
      constant `c`;
    - evidence at larger `n`, where 2-of-3 percolation can chain overfold
      pairs over long distances.

    Homological certificates do not transfer to `deep`, for two reasons:
    - `L_j` is not a free factor. Its abelian image is all of `Z^2`, so no
      nontrivial character kills it.
    - `H_1(K') → H_1(H)` need not be injective.

    For the same reason, the 1-dimensional local-system bound on `law` does
    not bound `deep`.
- **2026-09-19, swarm-0917-w17-w17-fp-pull (reframer + compute scout):
  OPEN; one lemma proved, one route killed, exact checks made
  `Q`-universal.** Details are in
  `research/artifacts/fpbs-overfold-free-fold-2026-09-19.md`, with scripts
  in `experiments/fpbs-overfold-free-fold-2026-09-17/`.
  - **Free-fold form (proved, Proposition 1).** Let `K` have index `d` in
    `L_{j+1}`. A seed is a vertex pair of `Γ_K`, and `J = ⟨K, g_1..g_k⟩`
    is the result of `k` seed folds. Call `J` realizable if
    `J ∩ L_{j+1} = K`, and a hit if `[L_j : J ∩ L_j] = d`.
    - (F) says: every realizable hit has `rk(J ∩ L_j : K) ≤ k`.
    - (O) implies (F), using M. Hall's theorem to build a finite-index
      `S ⊇ J` with `S ∩ L_j = J ∩ L_j`.
    - (F) implies (O) on every `L_j`-orbit that is a single
      `L_{j+1}`-orbit, in every finite `Q`.
    - So exact checks of (F) at fixed `d` hold for all `Q`, of any size.
      They do not reach cross-orbit levels.
  - **Exact verification.** Two scripts do the checks:
    - an all-class single-seed scan, `all_single.py`: 0 realizable
      overfold hits for `d ≥ 2`;
    - an exact two-seed BFS on the three law-3 classes at `d = 6`,
      `level2.py`: no law-3 `K'` is reached.

    Together they give (O) on coincident orbits of size `d ≤ 6` for
    `j = 1`, and `d ≤ 4` for `j = 2`, in every finite `L`-set.
  - **No-drop lemma (proved, Lemma 2).** Every hit has
    `δ = rk K + k − rk J ≥ 1`.
    - Suppose `δ = 0`. Hopficity gives `J = K * ⟨g⟩` and
      `J = K' * ⟨g⟩`, because `rk K = rk K' = d + 1`.
    - Killing the `g_i` then maps both `K` and `K'` isomorphically onto
      the same quotient, so `K = K'`.
    - That is impossible, since `[L_j : L_{j+1}] = ∞`.
  - **Conjecture (R)** is the missing input for the level-1 case of (O),
    which is `deep = 1 ⇒ law = 1`, for all `j` and `d`.
    - (R) says a realizable single overfold seed with `d ≥ 2` never drops
      rank. Lemma 2 then does the rest.
    - It is checked for `j = 1, d ≤ 5`; `j = 2, d ≤ 4`; `j = 3, d ≤ 2`.
    - It is false at `d = 1`, where it is harmless.
    - Two proof routes fail on the data: the closure is not a matching of
      the tree type, and SHNC equality does not force finite index.
  - **Conjecture (O')** is `law(K') ≤ δ(J)`. It implies (F). There are 0
    violations in the depth-2 runs.
  - **Where it dies: the retract route (G) is false.** (G) says `K'` is a
    retract of every witness `J`, or a free factor, or split in `H_1`.
    - The first law-2 level already refutes it: `j = 1`, `Q = Z/3` with
      `a = +1` and `b = −1`, so `law = 2`.
    - Two seeds give `J = S`. The map `H_1(K') → H_1(S)` has determinant
      −4, computed independently by Reidemeister–Schreier in
      `check_nonsplit.py`.
    - So no proof of (O) can go through a map `J → K'` that fixes `K'`.

- **2026-09-19, swarm-0917-w17-w17-fp-last1 (census-computation).** Exact C
  solver on the hardest known levels. No counterexample; the target stays
  OPEN. Details are in
  `research/artifacts/fpbs-overfold-exact-c-census-2026-09-19.md`.
  - *Tools.* `export.py` writes instances, and `deep.c` searches them.
    - The search is an exact breadth-first search over fold-closed
      partitions, reduced by the lifted automorphisms of `Q`.
    - `check_auts.py` verifies that those automorphisms are valid.
    - The lawful-only mode reproduces every known `law` value.
  - *Order-12 three-orbit Cayley level*, `(0,1,2,4,3),(1,0,3,4,2)` at
    `j = 1` (`run12_j1_cap5.txt`):
    - `law = 6`, and all-seed search is exhaustive up to 5 seeds, covering
      793171 states and 114216624 extensions;
    - so `deep = 6 = law`. w16 had only reached `deep ≥ 4`.
  - *The two `n = 24` three-orbit levels with `law = 6`*,
    `(0,1,3,2),(1,2,0,3)` and `(1,2,3,0),(0,2,3,1)`: `deep ≥ 5` for both
    (`run24a_cap4.txt`, `run24b_cap4.txt`).
  - *Census over the 54 Cayley levels of `local_cayley24_j1.txt`*
    (`census.py`):
    - at `j = 1`, `deep = law` exactly on every level with `law ≤ 5`;
    - every level with `law ≥ 6` has `deep ≥ 4`, and the three `law = 6`
      levels have `deep ≥ 5`;
    - at `j = 2` (`V ≤ 256`), `deep = law` wherever `law ≤ 4`.
  - *Lemma A (proved).* Fold consequences of a lawful pair are lawful, and
    those of an overfold pair are overfold, because `Γ_j(Q)` is folded.
    - Lawful identifications from overfold seeds therefore arise only by
      transitivity, along cycles of overfold orbits through `Γ_j(Q)`.
  - *Hanna Neumann counting is vacuous (proved).*
    - The strengthened Hanna Neumann inequality for `H = ⟨K, seeds⟩` and the
      rank-2 group `L_j` gives only `deep ≥ |p·L_j| − |p·L_{j+1}|`, summed
      over components. That is the orbit-count bound.
    - The other double-coset terms are unforced, since `L_j` is malnormal.
    - So on towers with `o(|Q|)` orbits of `L_{j+1}`, this route cannot give
      the floor.
  - *Remaining.* The weak form `deep ≥ c · law` has to use the double-coset
    restriction on seeds, or the cycle structure from Lemma A.
- **2026-09-19, swarm-0917-w17-w17-fp-break (belief breaker): OPEN; no
  counterexample; (O) reduced to its level-0 part.** Details:
  `research/artifacts/fpbs-overfold-depth-shift-reduction-2026-09-19.md`.
  Scripts: `experiments/fpbs-overfold-breaker-2026-09-17/`.
  - **Levels.** The level of a seed type at depth `j` is the largest `i`
    with equal images in `C_i`. Equivalently, `g = u_c u_{c'}^{-1} ∈ L_i`.
    - Level `j` is the lawful type.
    - At depth `j` there are `N_{j-i}` types of level `i`, with
      `N = 1, 11, 76, 472, 2821` (`j ≤ 4`).
    - Level-0 types have tree size `≤ 3`.
  - **Lemma D (depth shift).** Let `deep_j^{≥i}` allow only seeds of level
    `≥ i`. Then

    ```text
    deep_j^{≥i}(Q) = deep_{j-i}(Q^{(i)})   and   law_j(Q) = law_{j-i}(Q^{(i)}).
    ```

    - *Proof.* From the relative-rank form above: level `≥ 1` means
      `g ∈ L_1`, and `φ` transports `(S ∩ L_1, K, K')` to the depth-`(j−1)`
      data of `Q^{(1)}`. The one extra input is the double-coset identity
      (T_j): `U_j ∩ L_1 = φ(U_{j-1})`, where `U_j` is the union of the
      realised double cosets of `L_{j+1}`.
    - (T_j) is basis-dependent: minimal subtrees in `T(L; a, b)` versus
      `T(L_1; a, t_1)`. It is checked exactly for `j ≤ 4` by a
      tree-projection test (`doublecoset_check.py`).
    - Scope: `L_{j+1}`-transitive `Q`.
    - Independent check: `reduction_check.py` gives matching closure and
      promotion fingerprints on 22 random `Q`.
    - Dead end, recorded: the naive proof via principal pairs fails, since
      1, 9 and 64 level-≥1 types contain no principal pair
      (`principal_types.py`).
  - **Corollary.** (O) is equivalent to (O'_j): `deep_j(Q) = deep_j^{≥1}(Q)`
    at every depth. That is, only the level-0 overfold types need to be
    ruled out; all deeper types follow by induction. This is proved for
    `j ≤ 4`, and for all `j` given (T).
    - Caveat: the weak form `deep ≥ c·law` does not follow from a weak
      level-0 bound, which only compounds to `c^j`.
  - **Measure form (proved, all `j`).** `Q_j(X) ≤ Q_{j-1}(X^{(1)})` and
    `Q_j^law(X) = Q_{j-1}^law(X^{(1)})`, because graphings inside
    `E_{X|L_1}` are exactly the level-≥1 seeds.
    - For Bernoulli `ρ`, `ρ^{(1)} ≅ ρ`, so `Q_0(ρ) ≥ Q_1(ρ) ≥ …` is
      non-increasing, and `Q_j^law(ρ) = Q_0(ρ)`.
    - (O) at `ρ` says this sequence is constant. The floor says its limit
      is positive.
  - **Census, 0 FLAGs.** The pullback-model seed reducer `smallk.py`
    (validated against `exh_n5_j2`) ran on:
    - every transitive `Q` with `(j, n) = (1, 7)`: 4163 classes;
    - every transitive `Q` with `(j, n) = (2, 6)`: 624 classes;
    - every transitive `Q` with `(j, n) = (3, 4)` and `(4, 3)`;
    - random samples: `j=1, n=14` (300 levels) and `j=2, n=9` (100 levels),
      with pairs;
    - random samples, single seeds only: `j=3, n=8` and `j=4, n=5`.

    Throughout, `deep = law` whenever `law ≤ 2`.
  - **Where it dies.** No sharing mechanism is observed. A minimal
    counterexample must use a level-0 seed in every minimal witness, so a
    future hunt can be restricted to those.
- **2026-09-19, swarm-0917-w17-w17-fp-follow (compute scout,
  probability-random): OPEN; large-n evidence on the witness towers; new
  inductive decomposition (O-rel)/(O-step).** Details are in
  `research/artifacts/fpbs-overfold-cascade-2026-09-19.md`, with scripts in
  `experiments/fpbs-overfold-cascade-2026-09-17/`.
  - **No overfold cascade on random lifts.**
    - Random-order promotion on 2-permutation levels:
      - `j = 1`, `n = 20000`: lawful seeds `0.157 n`, overfold `0.533 n`,
        all types `0.51 n`;
      - `j = 2`, `n = 5000`: lawful `0.157 n`, overfold `1.26 n`.
    - Greedy search over all types (`j = 1`, `n = 1000`, 300 candidates per
      step) chose 0 overfold seeds, finishing at `0.112 n` against
      `0.114 n` lawful-only.
    - This is evidence only; random order and greedy are not the minimum.
  - **Decomposition.** Let `ℓ(P)` be the least number of lawful seeds whose
    closure contains `cl(P) ∩ ker m`.
    - (O-rel): `ℓ(P) ≤ |P|` for every finite seed set `P`.
    - (O-step): every nonempty `P` has some `s` with
      `ℓ(P) ≤ ℓ(P − s) + 1`.
    - (O-step) ⇒ (O-rel) ⇒ (O). The weak forms with a constant `C` give
      `deep ≥ law / C`, which is what step 5 of the route needs.
    - (O-rel) is (F) of the free-fold entry, extended from realizable hits
      to all seed sets. That extension is what lets induction on `|P|`
      pass through non-hit intermediate families.
  - **Checks (0 violations).**
    - 56,200 clustered or whole-level seed sets, pure and mixed, `j = 1, 2`;
      20,832 of them have a nontrivial lawful part.
    - All of these satisfy the certified bound `ℓ ≤ |P| − 1`. Strictness
      is proved for one overfold seed on tree-like levels, via Lemma A.
    - 9,600 one-step tests: the jump `ℓ(P) − max_s ℓ(P − s)` is always 0
      or 1. These values are upper bounds, so this part is heuristic.
  - **Where it stands.** No proof of (O-step). A single `P` with
    `ℓ(P) > |P|` on any finite `Q` would kill this decomposition, though
    not (O) itself.
- **2026-09-19, swarm-0917-w17-w17-fp-follow (calibration / obstruction):
  OPEN; a rank-3 obstruction to every structural proof; (O) on transitive
  `Q` reduced to a relative-inertia statement (RI_{L_j}).** Details are in
  `research/artifacts/fpbs-overfold-other-chains-2026-09-19.md`, with
  scripts in `experiments/fpbs-overfold-other-chains-2026-09-17/`.
  - **Lemma 1 (proved).** Take a general nested pair `A ≤ B ≤ F` and an
    `A`-transitive `Q`. Put `S = Stab(p)`, `K = S ∩ A` and
    `K'' = π_1(m Γ_A)`, so `K ≤ K'' ≤ S ∩ B`. Then:
    - `law = rk(K'' : K)` with unrestricted generators, via the domination
      lemma of [[fpbs-word-chords-are-dominated-by-merges]];
    - `deep ≥ min{k : g_i ∈ S, ⟨K, g_1..g_k⟩ ⊇ K''}`.
  - **Obstruction (proved, and checked by exact computation).** Every step
    used so far fails once `rk B ≥ 3`.
    - Let `B = ⟨a², b, aba⁻¹⟩` and `A = ⟨b, a⁴, ab²a⁻¹⟩` on `Q_n = Z/n`, with
      `n` odd. Then `deep = 1` (the single seed `a^n`) and `law ≥ n + 1`
      (the mod-2 cokernel). So `law / deep` is unbounded.
    - A malnormal `B` of rank 3 at `Q = point` has `deep = 1 < 2 = law`.
    - There are 175 gaps with both `A` and `B` malnormal in `F`, including
      `rk A = rk B = 3`. 147 of them carry independent certificates.
  - **Consequence.** Take any argument for `deep ≥ law`, or for
    `deep ≥ c · law`, that uses only fold or pullback structure, Lemma A,
    malnormality, equal ranks, orbit counting or `F_p`-homology. Such an
    argument is refuted by these pairs. It dies where
    `J = ⟨K, g⟩ ⊇ K''` has to be converted into generators of `J ∩ B`
    over `K`.
  - **Reduction (Proposition 3, proved).** State (RI_B) as:
    `rk((J ∩ B) : X) ≤ rk(J : X)` for `X ≤ B ∩ J`.
    - If `m` is onto and (RI_{L_j}) holds for `X = K`, then `deep ≥ law`
      on transitive `Q`.
    - (RI, C) gives `deep ≥ law / C`.
    - (F) of fp-pull is (RI) restricted to realizable hits.
    - (RI) involves no `Q` and no `φ`. For `X = 1` and `rk B = 2` it is
      inertia, which follows from SHNC (background, not re-proved here). It fails for every
      rank-3 `B` tested.
  - **Evidence.**
    - The homological necessary condition for (RI) has 0 violations in
      170,000 trials with `rk B = 2`. It is sharp: `c = k` occurs often.
      At `rk B = 3` there are 982 violations in 5000 trials.
    - All named rank-2 chains (`psi_*`, `n = 5, 6`) give `deep = law`.
    - The doubly malnormal random pairs with `rk B = 2` show 0 gaps in 9400, against 175 in 12,400 with `rk B ≥ 3`.
  - **Where it stands.** The missing step is (RI_{L_j}) for `X ≠ 1`. A
    rank-2 counterexample to (RI) would kill this route, but not (O). In
    that case a proof would need `φ`-specific input, for example (T_j) of
    fp-break.
- **One-level projection (w18-fp-last1, 2026-09-19). Status: open.**
  Details are in
  `research/artifacts/fpbs-overfold-level0-projection-2026-09-19.md`.
  Code and data are in `experiments/fpbs-overfold-projection-2026-09-17/`.
  - **Reduction (proved).** Let `ℓ_1(P)` be the least number of level ≥ 1
    seeds whose closure contains `cl(P) ∩ ker p_1`. Define:
    - (O'-rel): `ℓ_1(P) ≤ |P|` for every seed set `P`;
    - (Z1): `ℓ_1(P) ≤ |P| − 1` whenever `P` contains a level-0 seed.

    Then (Z1) ⇒ (O'-rel), and (O'-rel) ⇒ (O'_j), since `ker m ⊆ ker p_1`.
    With Corollary R of the depth-shift reduction, (O'-rel) at every
    depth `≤ j` gives (O) on `L_{j+1}`-transitive `Q` for `j ≤ 4`.
    At `j = 1`, (O'-rel) is exactly (O-rel). For `j ≥ 2` the two are not
    comparable a priori.
  - **Computations (0 violations).**
    - Exact runs at `j = 2` and hill-climbs at `j = 1, 2, 3`: no
      violation of (Z1) or (O'-rel).
    - Single level-0 seeds (145k tested): never fold a level ≥ 1 pair
      unless `Q` has a common fixed point of `a` and `b`. This is data
      only; the proof is not written.
    - (S_law) is (O-rel) restated. The runs confirm it but add nothing.
  - **Obstruction.** Hill-climbs attain `ℓ_1 = |P| − 1` exactly (`k = 4`
    and `k = 6`). This refutes `ℓ_1 ≤ ⌈|P|/2⌉`. It also rules out, for
    these `k`, any argument that charges each level-0 seed a weight
    `c < 1`. What remains is an exact one-for-one exchange, (O-step)
    projected to one level.
- **2026-09-19, swarm-0917-w18-w18-fp-pull (host-geometry): OPEN.** The
  depth-shift reduction is now unconditional at every depth: (T_j) is proved
  for all `j ≥ 1`. Details are in
  `research/artifacts/fpbs-doublecoset-transport-all-depths-2026-09-19.md`,
  with scripts in `experiments/fpbs-doublecoset-transport-2026-09-17/`.
  - **Lemma 1 (proved).** The minimal subtree of `L_{j+1}` is the φ-image
    of the minimal subtree of `L_j`, in `T(L; a, b)`, with its leaves
    pruned.
    - Every vertex of `Y = T_{L_1}` is `φ(w)`, `φ(w)b` or `φ(w)b²`.
    - A `b`-edge maps to `f(w) → α(w) → β(wb) ← α(wb) ← f(wb)`.
    - The only leaves are the `φ(v)` whose link is `{b, b⁻¹}`, and no
      further pruning is needed.

    This gives an explicit recursion `C_{j+1} = Exp(C_j)`. It is checked
    against Stallings folding for `j ≤ 8` (`transport_j9.txt`).
  - **Proposition 2 (proved).** Let `B` be a leafless subtree and `h ∈ L`.
    The φ-expansions of `B` and `hB` can miss each other while `B` and `hB`
    meet in only one way: they meet in a single vertex whose two links are
    `{b, b⁻¹}` and `{a, a⁻¹}`.
  - **Lemma 3 (proved).** No core `C_j` has a vertex with link `{a, a⁻¹}`.
    Proof by induction: type-1 and type-2 vertices never carry `a⁻¹` and
    `a` together.
  - **Theorem 4.** (T_j) holds for every `j ≥ 1`.
    - So Lemma D holds for all `j` and `i ≤ j`.
    - So does Corollary R: (O) at depth `j` is equivalent to (O'_j), for
      `L_{j+1}`-transitive `Q`, modulo the cited relative-rank form.
  - **Independent check.** `doublecoset_check.py` now reports SET EQUAL for
    `j ≤ 6`, with 3381 and 19992 types at `j = 5, 6`
    (`doublecoset_j6.txt`).
  - **Where it stands.** Three things remain open:
    - level-0 domination (O'_j) itself;
    - the intransitive scope;
    - the uniform weak form. A weak level-0 bound still compounds to `c^j`.

    By Lemma 1, level-0 seeds are the `g ∉ L_1` with
    `T_H ∩ g T_H ⊂ Y ∩ gY ≠ ∅`. So a proof of (O'_j) can work entirely
    inside the bounded overlaps of `L_1`-translates of `Y`.

**2026-09-19, swarm-0917-w19-w19-fp-last1 (finite-models): non-abelian
quotient test of rank-2 relative inertia. OPEN.**
- **Target.** The w17 calibration reduced (O) on `L_{j+1}`-transitive `Q` to
  (RI_{L_j}): `rk((J ∩ L_j) : X) ≤ rk(J : X)`. It asked for a proof for
  rank-2 `B`, or a rank-2 counterexample. Its only evidence was mod-`p`
  homology.
- **Result: (RI_B) is false for rank-2 `B` (hand proof).**
  - Take `B = ⟨b, c⟩` with `c = a b² a⁻¹`, and `X = ker(B → S3)` for
    `b ↦ (123)`, `c ↦ (12)`.
  - `J = ⟨X, a⟩` contains `b³` and `b⁴ = a⁻¹ c² a`, so `J = F ⊇ B`.
  - So `rk(B : X) = d(S3) = 2 > 1 = rk(J : X)`.
  - The mod-`p` cokernel is `H_1(S3; F_p)`, of dimension at most 1, so every
    homological test is blind to this failure.
  - The failure uses non-malnormality: `a⁻¹ ⟨c⟩ a ≤ B`.
- **Lemma 2 (proved).** A violation with `J ⊇ B` forces `J = ⟨B, g⟩` with
  `rk J = rk B` and `J ≠ B`. For rank 2 this means `[J : B] = ∞`.
- **Hunts** (`searchB.py`, `searchC.py`, `searchD.py`), with quotients
  `S3`, `A4`, `A5`:
  - **Rank 3:** violations in most trials, malnormal or not.
  - **Rank 2, not malnormal:** 33 of 198 subgroups violate. All 9 hits in the
    unfiltered run were checked and are non-malnormal.
  - **Rank 2, malnormal:** 0 of 356 random subgroups; 0 for `L_1` (all
    `S3` quotients, `|g| ≤ 7`) and for `L_2`.
  - **The case (O) needs:** `B = L_j` with `X` of finite index in `L_{j+1}`
    (`L_{j+1}` itself or `ker(L_{j+1} → S3/A4)`), at `j = 1, 2`. There were
    0 violations in 11,080 pairs `(X, g)`, with `F_2`/`F_3` and `S3`
    lower bounds for `rk(J ∩ L_j : X)`.
- **What dies.** Every proof of exact (RI_{L_j}) built only on
  `rk L_j = 2` is refuted by the example above. That includes inertia,
  strengthened Hanna Neumann, rank-2 Nielsen/Whitehead arguments and mod-`p`
  homology. With the w17 rank-3 malnormal gaps, neither "rank 2" nor
  "malnormal" suffices alone. In all data, only the conjunction has 0
  violations.
- **What survives.**
  - The example has ratio exactly 2, and `searchD` found no rank-2 ratio
    above 2. So `(RI_B, 2)` is intact, and by w17 Proposition 3 it would
    give the weak form `deep ≥ law / 2`, which is enough for the floor route.
  - Proposed split into independent pieces: (RI-mal), meaning (RI_B) for
    malnormal rank-2 `B`; and (RI-C), meaning `(RI_B, 2)` for all rank-2 `B`.
- **Artifact.** `research/artifacts/fpbs-overfold-rank2-relative-inertia-2026-09-19.md`.
- **2026-09-19, swarm-0917-w19-w19-fp-break (belief breaker,
  minimal-counterexample): OPEN; (O-step) is REFUTED by an exact
  counterexample; (O-rel) survives exhaustively for `|P| ≤ 3`; `ℓ` is not
  subadditive.** Details are in
  `research/artifacts/fpbs-overfold-cap5-2026-09-19.md`, with code and
  outputs in `experiments/fpbs-overfold-cap5-2026-09-17/`.
  - **(O-step) is false.**
    - Take j2law8, the Cayley level of `(0,2,3,1),(1,2,0,3)` at `j = 2`
      (`V = 240`, `law = 8`), and the overfold seeds `s = (9,80)` and
      `t = (215,58)`.
    - `ℓ({s}) = ℓ({t}) = 0`, by Lemma A.
    - `ℓ({s,t}) = 2`:
      - none of the 192 lawful pairs covers `cl({s,t}) ∩ ker m` on its own;
      - the two lawful seeds `(2,69),(2,133)` do cover it.
    - So no `x ∈ P` has `ℓ(P) ≤ ℓ(P−x) + 1`.
    - This is checked exactly by `lcheck.c`, and independently by
      `ostep_verify.py`, a separate Python fold closure that tests every
      lawful pair (`ostep_verify_j2law8.txt`). `repcheck.py` confirms that
      the lawful representatives cover all 12 lawful single-seed closure
      classes, so `ℓ` is exact.
    - Exhaustively, 108 of the 544,446 overfold pairs on j2law8 behave this
      way. (The w17-follow one-step tests used upper bounds on `ℓ` and so
      could not see this.)
  - **What this kills.** Any proof of (O-rel) or (O) that adds seeds one at
    a time with a unit budget per seed fails. This includes exchange or
    matroid-rank induction through `ℓ`, and anything using subadditivity of
    `ℓ`: two individually inert overfold seeds can together force a lawful
    pair that costs two lawful seeds.
    - There is also synergy of order three: 3219 overfold triples on j2law8
      and 531 on j2law6b have `ℓ = 2` while every sub-pair has `ℓ = 0`. So
      `ℓ` is not dominated by a sum of pair terms either.
  - **Replacement decomposition (O-pair), which survives.** (O-pair) asks
    for some `s` with `ℓ(P) ≤ ℓ(P−s) + 1`, or some pair `{s,t}` with
    `ℓ(P) ≤ ℓ(P−s−t) + 2`.
    - It still gives (O-rel), by induction on `|P|` using `ℓ({s}) ≤ 1`, and
      hence (O).
    - 0 violations: all 256 subsets of three forced 8-seed witnesses, and
      all 47,276,061 overfold triples (first seed up to the lifted
      automorphisms) on each of the three `V = 240` levels.
  - **(O-rel) holds exhaustively for `|P| ≤ 2` and for overfold-only
    `|P| = 3`** on j2law8, j2law6a and j2law6b. For overfold `P` it is
    strict: `ℓ ≤ |P| − 1`.
    - It is tight, `ℓ = |P|`, on forced witnesses. `beam ... force`, which
      bans lawful seeds at level 1, reaches the goal of j2law8 at exactly
      `8 = law` with 6 overfold + 2 lawful seeds. The 6-overfold part has
      `ℓ = 6`, splitting into three pairs of `ℓ = 2`.
    - Observed, not claimed: `ℓ(P) ≤ 2⌊|P|/2⌋` for overfold-only `P`.
    - Every pair of one lawful and one overfold seed has `ℓ = 1`.
  - **No counterexample to (O) on the easy targets.**
    - Heuristic all-seed beam searches (not exhaustive) reach exactly `law`,
      with lawful witnesses:
      - on the three j=2, `V = 240` levels (law 8, 6, 6);
      - on all 21 j=2 Cayley levels with `V > 256` that the w17 census
        skipped (`sweep_wide_B1000.txt`).
    - `law` itself is exact on all 21 of those levels (the lawful-only beam
      never truncated).
  - **Cap 5 on inst24a and inst24b** (the `j = 1`, `V = 192`, law-6 levels
    with `deep ∈ {5,6}`): exhaustive, with no goal within 5 seeds on either.
    So `deep = law = 6` on both, and (O) holds there.
    - The level-5 extension counts are `8,777,155 × 288` and
      `8,777,114 × 288`.
    - The search uses `deep5fp.c`: `deep5` with the last stored level kept
      as 128-bit fingerprints, and its states regenerated. On each level the
      fingerprint count equals a full-key `deep5` count, so the fingerprints
      are injective and the search is exact.
    - Every `j = 1` census level with `law ≤ 6` now has `deep = law`.
  - **The `j = 1` law-8 level `(0,2,3,1),(1,2,0,3)`** (`n = 12`, `V = 96`):
    exhaustive, with no goal within 6 seeds, so `deep ≥ 7` (the census had
    `≥ 4`).
    - A beam with `B = 10^6` reaches the goal only at `8`.
    - Five more `j = 1` census levels with `law ≥ 8` remain at `deep ≥ 4`,
      as do the three `j = 2`, `V = 240` levels at `deep ≥ 3`.
  - **Where it dies.**
    - The claim stays OPEN. The decomposition (O-step) is dead, and so is
      every unit-increment or subadditive induction on `ℓ`.
    - What survives is (O-rel), with (O-pair) as the step lemma. The first
      thing to prove is a two-overfold-seed statement: `ℓ(P) − ℓ(P−A) ≤ |A|`
      for some `A ⊆ P` with `|A| ≤ 2`.
    - A counterexample to (O-rel) needs an overfold set whose `ℓ` exceeds
      its size. None exists for `|P| ≤ 3` on these levels, so a hunt must
      start at `|P| ≥ 4`.
- **2026-09-20, swarm-0917-w20-w20-fp-last1 (logic-computability): OPEN;
  the k = 1 layer of the chain (RI_{L_j}) ⇒ (G_j) ⇒ (O) is now finite and
  exact, and (W) is refuted.** Full write-up:
  `research/artifacts/fpbs-overfold-one-pair-joins-2026-09-19.md`.
  - **Lemma 1 (one-pair lemma), proved.** For f.g. `X` and any `g`, the
    join `<X, g>` falls in one of two cases.
    - Arc case: `Γ_X` embeds in `Γ_{<X,g>}` and the rank goes up by one.
    - One-pair case: `Γ_{<X,g>} = fold(Γ_X / (u ~ w))` for two vertices
      `u, w`.

    Validated by direct folding: 1846 one-pair and 1110 arc cases,
    0 mismatches.
  - **Arcs are harmless.** For every rank-2 host `B`, malnormal or not, an
    arc join satisfies `rk(J ∩ B : X) ≤ 1`. The proof uses SHN
    (`rk Y ≤ rk X + 1`) and Kurosh (`X` is a free factor of `Y`).
  - **Exact decidability.** (RI_B) at `k = 1`, E(2), (Mon_φ) at `k = 1`
    and (W) each reduce to at most `C(|V|, 2)` folds, with no bound on
    `|g|`. This supersedes the `|g| ≤ 7` searches of w18 and w19.
  - **Lemma 2 (φ-expansion dictionary).** It gives `Γ_{φ X_0}` in closed
    form, verified on 3000 random cases.
  - **Type lemma.** Same-type pairs of the expansion give joins inside
    `L_1`. Only the three mixed double cosets can reach `F`.
  - **(W) of w19-follow is REFUTED.** Take `X_0 = <aBAB, ABaba>`. Then
    `g = AbbbaBBa` (`|g| = 8`) gives `<φX_0, g> = F`, while
    `<X_0, a> ≠ F` and `<X_0, b> ≠ F`. The exact censuses found 302
    violations in total. Proof routes through "`a` or `t` completes" are
    dead.
  - **Exact censuses, all `g` at once (0 violations).**
    - (Mon_φ) at `k = 1`: 0 violations in 35498 E(2)-hits.
    - (RI_{L_1}) at `k = 1`: 0 violations in 146567 one-pair joins,
      including 18,909 with `Y ≠ X`.
    - (RI_{L_2}) at `k = 1`: 0 violations in 18313 joins, including 491
      with `Y ≠ X`.
    - Self-test: the same code finds 72 violating one-pair folds for
      w19-last1's non-malnormal host and 0 for `L_1`.
  - **Gap.**
    - `k ≥ 2`: arc-then-fold joins form an infinite family.
    - A proof of (Mon_φ) at `k = 1`, as a transfer for mixed collapsing
      pairs. Simple projection works in only 142 of 283 hits.
- **2026-09-20, swarm-0917-w20-w20-fp-break (belief breaker, operator-algebras /
  spectral): OPEN; the direct route "run the (W) proof on deep" is dead at
  every `j ≥ 1`.** Details are in
  `research/artifacts/fpbs-overfold-spectral-percolation-2026-09-19.md`, with
  scripts in `experiments/fpbs-overfold-spectral-percolation-2026-09-17/`.
  - **Exact model (proved, validated with 0 mismatches against the fold
    closure).** `deep_j` is 2-of-3 bootstrap percolation on atoms
    `Q × {pair types}`, with hyperedges `Q × {triangle types}`.
    - Triangle types are the components of the distinct-triple graph of
      `C_{j+1}`. They are finite trees.
    - Compositions: `j = 1` has 12 atom types and 42 triangle types
      (1 `LLL`, 23 `LOO`, 18 `OOO`); `j = 2` has 88 and 836. There is never
      an `LLO` type.
    - `law_j` only uses the `LLL` type, `(y, y a^{-1}, y t_j^{-1})`.
  - **Spectral relaxation fails.** The multi-type version of Lemma 2 of
    (W) needs `λ < 1`. At `j = 1` on a random level, `λ = 3.55`, against
    `0.83` at `j = 0`. The average pair-weight per atom type is forced
    to be 7.
  - **Class kill (Proposition K, exact word count).** In the Cayley tree at
    `j = 1`, the block `B_2 × {all types}` has 226 full hyperedges on 204
    atoms.
    - The ratio is 1.108, 1.197 and 1.225 at radius 2, 3 and 4; at radius 2
      it is at least 3.21 for `j = 2`. At `j = 0` the ratio tends to 1/3.
    - Disjoint packings exist on every locally tree-like tower, which
      includes every essentially free profinite witness. They give sets with
      `F(A) > |A|` at every size up to about `1.27 n`.
    - So Lemma 1 plus any upper bound on full hyperedges proves only
      `deep ≥ O(1)`.
    - Type weights do not help. An LP over weights against the blocks
      `B_r × I` has optimum excess `t* = 1.29` for `r ≤ 2` and `t* = 2.36`
      for `r ≤ 3`.
  - **Where it dies.** At Lemma 2: the overfold hypergraph is locally
    supercritical, and increasingly so with `j`. A proof of the floor
    therefore has to use the order structure of reachable closures, such as
    (O), (O-step) or (RI). A density or counting certificate cannot work.
    None of this refutes (O).
- **2026-09-20, swarm-0917-w20-w20-fp-follow (compute scout / follow):
  OPEN. (RI_B) at k = 1 holds on random malnormal hosts and in the (G_1)
  regime. Every known violation fails only the "one fibre pair" half.**
  Full write-up:
  `research/artifacts/fpbs-overfold-malnormal-host-census-2026-09-20.md`.
  - **Exact k = 1 censuses: 0 violations on malnormal hosts.** The census
    covers 1333 host instances and 13893 joins with `Y ≠ X`.
    - Random malnormal rank-2 hosts of infinite index: 562 hosts, 1500
      joins with `Y ≠ X`, 0 violations. None of these hosts is a φ-level.
    - `B = L_1` with `X` of finite index in `L_2`, the (G_1) input:
      10947 joins with `Y ≠ X`, 0 violations.
    - `L_1`: 1446 joins with `Y ≠ X`, 0 violations.
    - Every nontrivial `Y` was a one-pair fold of `Γ_X`, never an arc.
    - Calibration: non-malnormal hosts give 20 violations from 3 of 148
      hosts, all with `X` normal in `B`.
  - **k = 2 and 3, certified by sampling.** In the (G_1) regime, 823
    joins have `rk(Y:X) = 2` exactly, and all are certified `≤ 2`. A
    further 2512 joins with 2 or 3 pairs over four host types are all
    certified `≤ npairs`: 0 uncertified.
  - **Lemma (proved).** Let `m = (q,f) : Γ_X → P = core(Γ_J × Γ_B)`.
    Then `ker m = ≈ ∩ ker f` is fold-closed, and
    `Z = π_1(m Γ_X) = <X, jumps across ker m> ≤ Y`. If `f(u) = f(w)`,
    then `Y = J`. So all k = 1 content is in pairs with `f(u) ≠ f(w)`.
  - **Split.** (RI_B) at k = 1 follows from two claims:
    - (A) `Z = Y`;
    - (B) `ker m` is generated by one pair.

    Findings:
    - (A) held in all 1912 one-pair joins tested, on malnormal and
      non-malnormal hosts.
    - (B) held on all malnormal hosts.
    - **Each of the 21 known violations** (w19's `<b, ab^2a^-1>` plus the
      20 above) satisfies (A) and fails (B).
    - In multi-pair joins, (A) fails only as `Z = X`, `Y = <X, one arc>`
      (22 of 1585 cases). The total `rk(Y:Z) + rk(Z:X) ≤ npairs` still
      held in every case.
  - **Dead (proved).** The one-step induction
    (RI') `rk(<Z,g> ∩ B : Z ∩ B) ≤ 1` is false: take `Z = <b>`, `g = a`,
    `B = L_1`, where `<b> ∩ L_1 = 1`. So an induction on `k` cannot pass
    through `<X, g_1> ⊄ B`.
  - **Gap.**
    - Prove (A) at k = 1 for all `B`: every reduced loop of `P` lifts
      with jumps in `ker m`.
    - Prove (B) for malnormal `B`.
    - Their k-pair form, (Int_B):
      `r(≈_S ∩ ker f) + rk(Y:Z_S) ≤ |S|`, has the same shape as (O).
      It is finer, but not easier in kind.
- **2026-09-20, swarm-0917-w21-w21-fp-last1 (quantifier-shift): OPEN; this
  hole decides the flagship at `Gamma_mal` in both directions, through one
  savings density on the witness towers.** Proved from established nodes
  only. No new census.
  - **Monotone levels.** Let `X = lim Q_m` be essentially free profinite
    with transitive levels. By item 3 of
    [[fpbs-mal-depth-promotion-equals-overfold-merge-number]], `deep_j(Q)`
    is the least size of a level-`Q` chord set that works. A level-`Q_m`
    chord set is also a level-`Q_{m+1}` chord set, with the same measure
    `|Φ| / |Q_m|`. So `deep_j(Q_m)/|Q_m|` and `law_j(Q_m)/|Q_m|` are
    nonincreasing in `m`, and the infima in item 4 are limits.
  - **Savings density.** Put `σ_j(X) = Q_j^law(X) − Q_j(X)`, which equals
    `lim_m (law_j − deep_j)(Q_m) / |Q_m|`. Let `X_j` be the towers of
    [[fpbs-mal-twisted-level-seed-density-uniform-witness]], so
    `Q_j^law(X_j) ≥ 1/60`. Theorem M of
    [[fpbs-mal-promotion-cost-monotone-under-weak-containment]] gives
    `Q_j(X_j) ≤ Q_j(ρ)`. Hence
    `σ_j(X_j) ≥ Q_j^law(X_j) − Q_j(ρ)` and
    `inf_m deep_j(Q_m)/law_j(Q_m) ≤ 60 · Q_j(ρ)`.
  - **Dichotomy.** Let `θ_j = σ_j(X_j) / Q_j^law(X_j)`, the fraction of the
    lawful seed density that overfold seeds save.
    - If `sup_j θ_j < 1`, then `Q_j(X_j) ≥ (1 − sup θ)/60` for all `j`.
      By the per-depth witness criterion of the Theorem M node, that is the
      floor. So it gives a counterexample through
      [[fpbs-mal-floor-gives-fixed-price-counterexample]], without needing
      (O) on any level outside the `X_j`.
    - If `Gamma_mal` has fixed price, which `fpbs-fixed-price-universal`
      asserts, then `Q_j(ρ) → 0`. This uses
      [[fpbs-mal-fixed-price-iff-bernoulli-finite-cost]] (1 ⇔ 6) and
      [[fpbs-mal-floor-iff-deep-promotion-floor]], where `Q_j` is
      nonincreasing. So `θ_j ≥ 1 − 60 · Q_j(ρ) → 1`: at large depth, overfold seeds save
      almost all of the lawful density. On fine levels,
      `law_j − deep_j ≥ (1/60 − ε)|Q_m|`.
  - **What is new.** The route asks for `deep ≥ c · law` on every finite
    `Q`. Only `sup_j θ_j < 1` on the levels of the `X_j` is needed. For
    example, any additive bound `law_j − deep_j ≤ o(|Q|)`, uniform in `j`,
    on those levels gives `θ_j = 0`. Conversely, the flagship predicts
    *linear* savings on those same levels at every large depth. Savings
    that are only a finite-size effect cannot rescue it. The census data
    (`deep = law` on all small levels) bound no `θ_j`, since `θ_j` is a limit
    over fine levels.
  - **Where it dies.** This is a sharpened target, not a proof. No bound on
    `θ_j` is proved. The next step is to bound `σ_j(X_j)` on the random
    `N`-lift towers. Their levels are locally tree-like, so the savings
    density is a local statistic of the lift.
- **2026-09-20, swarm-0917-w21-w21-fp-pull (fp-pull fallback worker):
  OPEN; (O) is reduced, for the floor, to a strictly narrower cross-orbit
  statement (O|B).**
  - *New established input.* [[fpbs-mal-sym-levels-embed-orbits-at-every-depth]],
    proved in its `-proof` route. For `d ≥ 3` and `j ≤ d − 2`, on the
    Cayley level of `Sym(d)` with `a ↦ (0 1)` and `b ↦ (0 1 ⋯ d−1)`:
    - `L_j` fixes `j` points and acts as `Sym(d − j)` on the rest;
    - every component of `Γ_j` embeds in the level, which is (E), and the
      same holds on every finite cover;
    - at `d = j + 2`, every `L_j`-orbit is `{g, gα}`, with `a` and `t_j`
      acting as the same swap.
    So on covers of `B_j = Cay(Sym(j+2))`, every overfold seed joins two
    **different** `L_j`-orbits, and the within-orbit overfolds do not occur.
    The proof uses a restriction lemma `φ^*X_d ≅ X_{d−1} ⊔ {pt}`, and a
    vertex-type induction on `C_j` in which reducing `φ(t_j)` cancels one
    pair per junction. `eb_family.py` checks it for `d = 4, …, 10`, and the
    bound `j ≤ d − 2` is sharp.
  - *New established input.* [[fpbs-mal-seed-density-towers-over-orbit-gapped-bases]].
    The random-lift tower of the uniform witness can be started at any
    transitive base `B` whose orbit-wise top eigenvalue satisfies
    `μ_j(B) ≤ λ_0`. The key step is that a good lift has invariant functions
    pulled back from `B`. Since `μ_j(B_j) = −1`, each depth has a tower of
    transitive covers of `B_j` with density `≥ 1/60`.
  - *Spectral note.* A single tower through every `B_j` cannot work
    spectrally. The orbit graphs `Cay(Sym(m), {(0 1), m-cycle})` have gaps
    `0.75, 0.19, 0.094, 0.054, 0.034, 0.023` for `m = 3, …, 8`
    (`spectral_sym_m3_m8.txt`). Theorem M allows per-depth witnesses.
  - *New route.* `fpbs-mal-depth-floor-from-sym-base-overfold-domination`
    goes to `fpbs-mal-bernoulli-single-stage-floor`. Its only open premise
    is [[fpbs-mal-overfolds-dominated-on-sym-base-covers]] (O|B):
    `deep_j ≥ c_1 law_j` on finite transitive covers of `B_j`. This node
    implies (O|B), not conversely.
  - *Exact evidence for (O|B), on the bases only.* Under (E), a minimum
    promoting set splits into blocks of orbits (`blocks.py`,
    `cayley_blocks.py` with `deep.c`). Every tested block has
    `deepc = Σ law`:
    - on `B_2`: all 11 two-blocks, all 55 three-blocks, and 83 of the 165
      four-blocks;
    - on `B_3`: all 59 two-blocks.
    No proper cover of `B_j` has been tested.
  - *Remark.* `deep_j` and `law_j` are at most `N`-fold along `N`-sheeted
    covers. So densities along a tower are non-increasing, and one bad cover
    poisons every tower through it.
  - *Where it stands.* This node is still OPEN, and so is (O|B). The next
    test is exact `deep_j` on small random transitive covers of `B_2` and
    `B_3`, for example 2- and 3-sheeted lifts.
- **2026-09-20, swarm-0917-w21-w21-fp-follow (host-geometry): OPEN. The
  image subgraph is a free factor. With Hanna Neumann this proves the
  Z = X branch of (RI_B) and reduces (RI,2) to one fibre statement. The
  image claim (A) is refuted.** Artifact:
  `research/artifacts/fpbs-overfold-free-factor-shn-2026-09-20.md`.
  Code: `experiments/fpbs-overfold-image-claim-2026-09-17/`.
  - **Lemma (proved).** `Z = π_1(m Γ_X)` is a free factor of
    `Y = J ∩ B`, because `m Γ_X` is a connected based subgraph of `P`.
  - **Theorem (proved).** If `rk B = 2`, then for every k-pair join,
    `rk(Y:X) ≤ rk(Z:X) + rk J − rk Z`. Proof: `rk(Y:Z) ≤ rk Y − rk Z`
    (free factor), and `rk Y ≤ rk J` (HNC, Friedman–Mineyev, background).
  - **Corollaries (proved).**
    - If `Z = X`, then `rk(Y:X) ≤ rk J − rk X ≤ k`. This is (RI_B) on the
      whole ZX branch, at every k, with no malnormality assumption.
    - Put (Fib): `rk(Z:X) ≤ rk(J:X)`. Then (RI_B) ⇒ (Fib), by the
      free-factor retraction, and (Fib) ⇒ (RI,2)_B for rank-2 `B`. By
      w17 Prop 3, (RI,2)_{L_j} is enough for `deep ≥ law/2` and the floor.
    - At k = 1 a mixed case `X < Z < Y` forces `rk Y = rk J = rk Z + 1`.
  - **(A) refuted (exact).** `B = <bab, b²a⁻²b⁻¹a⁻¹>` is malnormal. With
    `X = <b⁻¹a⁻¹b⁻¹>` and pair (0,1), `Y = B` but `Z = X`. It also fails
    on an onto malnormal host. (A) does hold when `[B:X] < ∞`: a proper
    free factor has infinite index. That explains the earlier k = 1 data.
    Every rank-2 k = 1 failure of (A) sampled is ZX, so the theorem covers
    it. w20 step 1 is dead as stated, and its ZX job is done.
  - **Where it dies.** On the ZY branch, (Fib) is (RI) itself, and it
    needs rank 2 and malnormality together.
    - Malnormal rank-3 hosts with `X = ker(B → S_3)` violate it at k = 1,
      with `Y = B`.
    - So do non-malnormal rank-2 hosts (10 of 1305 joins, `|G|` = 6, 12
      or 24).
    - Malnormal rank-2 hosts showed 0 violations in 872 joins.
    - Sharpest open instance: for malnormal rank-2 `B` and
      `X = ker(B → G)`, the image of `<X, g> ∩ B` in `G` is cyclic.
      `⟨⟨X⟩⟩_J ∩ Y = X` suffices. Dehn filling gives this for fixed `J` and
      deep enough `X`, but not uniformly over `J = <X, g>`.
- **2026-09-20, swarm-0917-w21-w21-fp-break (belief breaker,
  census-computation): OPEN; exact mid-n certification of deep = law, and
  the w19 law-8 lead squeezed to near-pure-overfold witnesses. 0
  violations.** Details are in
  `research/artifacts/fpbs-overfold-midn-exact-2026-09-20.md`, with code
  in `experiments/fpbs-overfold-midn-2026-09-17/`.
  - **Reduction (elementary, proved in the artifact).** Split a witness
    as `T = P ⊔ L`, with `P` overfold and `L` lawful. Let
    `lawneed(X)` be the least number of lawful seeds completing `X` to the
    goal. Then `deep < law` holds iff some overfold `P` with `|P| = s ≥ 1`
    has `lawneed(cl(P)) ≤ law − 1 − s`.
    - Testing all `s ≤ smax` decides `deep = law` exactly when
      `law ≤ smax + 1`.
    - Otherwise it proves that every witness of size `law − 1` has more
      than `smax` overfold seeds.
    - `rel.c` runs this with `P[0]` restricted to orbit representatives
      under lifted automorphisms, and decides lawneed by exact
      enumeration of lawful subsets.
    - Cross-checked against `deep.c` on `inst12` (law 6) and on a random
      `n = 20` law-4 level.
  - **Exact deep = law (every level certified).**
    - `j = 1`, `n = 20`: 300 random transitive levels, law histogram
      2:3, 3:228, 4:67, 5:2. Up to 9.5·10^7 P's per level.
    - `j = 1`, `n = 30`: 5 law-4 levels, 5.9·10^6 P's each.
    - `j = 2`, `n = 12`: 40 random levels, law histogram 2:25, 3:13, 4:2.
      Up to 1.9·10^8 P's per level.
  - **w19's law-8 level `inst12j1_law8`.** It has V = 96, 12 lawful and
    132 overfold seeds, and 11 orbit reps. Exhaustive `s ≤ 5` is clean,
    with 4,027,595 P's at `s = 4` and 128,883,040 at `s = 5`.
    - So every 7-seed witness there has at least 6 overfold seeds, i.e.
      at most 1 lawful one.
    - With w19's exhaustive `deep ≥ 7` (w19 lane, local commit
      `d011e9593c`, not on main), a counterexample on this level
      must be an almost purely overfold 7-set.
    - `rel` at `s = 6` and `s = 7` would decide deep there exactly, at
      about 3.3·10^9 and 6.9·10^10 P's: at most about 3 CPU-days and 2
      CPU-months at the measured rate. `s = 6` is a feasible dedicated
      job; `s = 7` needs better pruning.
  - **Structured levels.** On PSL(2,23) acting on P^1 (`n = 24`, `j = 1`),
    two law-6 levels are clean for `s ≤ 3`, with 3.0·10^6 P's at `s = 3`.
    So every 5-seed witness there has at least 4 overfold seeds.
    - High law appears to need structure. Random levels at `n ≤ 30`
      reach law 5 only rarely, while PSL(2,29) gives law 6 in 3 of 20
      levels.
  - **Where it stands.** This is evidence, not proof. Two things matter
    for the next attack:
    - small mixtures of overfold and lawful seeds never beat the law in
      any tested case;
    - a counterexample, if one exists, is a large, nearly lawful-free
      overfold family on a high-law structured level.
- **2026-09-20, swarm-0917-w22-w22-fp-last1 (census-computation): OPEN;
  first test of (O) on proper covers of the Sym base `B_1 = Cay(Sym 3)`,
  0 violations, and exact on every double cover.** Details are in
  `research/artifacts/fpbs-overfold-sym-covers-2026-09-20.md`, with scripts
  and outputs in `experiments/fpbs-overfold-sym-covers-2026-09-17/`.
  - **Target.** This is the restriction (O|B) that the w21-fp-pull route needs:
    `deep_j ≥ c_1 law_j` on covers of `B_j`. Until now only the bases
    themselves had been tested.
  - **Method.** Every 2-sheeted permutation-voltage cover of `B_1` was
    built, gauge-fixed on a spanning tree (128 choices), and run through the
    exact relative solver `rel` (w21-fp-break) at `j = 1`.
  - **Result.**
    - There are 127 transitive covers in 31 isomorphism classes. (E) holds
      on all of them.
    - The classes have `law` 3, 4, 5 or 6 (8, 14, 5 and 4 classes
      respectively).
    - **`deep_1 = law_1` holds exactly on all 31 classes.**
      - This is computer-checked: every `s ≤ law − 1` was run, and the exact
        reduction from w21-fp-break was applied.
      - The `law 6` classes needed all 5-sets of overfold seeds: 1.29 or
        3.87 · 10^8 sets each, in `law6_*_s5.txt`.
      - No saving appeared in any run.
    - `B_2` itself has `law_2 = 12` and is clean for `s ≤ 2`.
    - On double covers of `B_2` (`V = 960`), `rel` does not finish computing
      `law` in 300 s.
  - **Where it dies.**
    - This is finite-size evidence at `j = 1` only. It bounds no `θ_j` and
      gives no uniform `c_1`.
    - Exactness at `s = law − 1` costs about `C(#overfold, law − 1)`
      closures, which already puts `j = 2` (`law 12`) out of reach.
- **2026-09-20, swarm-0917-w23-w23-fp-last1 (linear-characteristic): OPEN;
  homological bounds at every depth computed exactly and killed as a class.**
  Details are in `fpbs-mal-depth-homology-certificates-are-fox-kernel-gaps`
  (ESTABLISHED), with scripts in `experiments/fpbs-transitive-retract-2026-09-17/`.
  - *Certificate (proved).* For every finite `Q`, every `j` and every field,
    `deep_j(Q) ≥ k_{u_{j+1}}(Q) − k_{u_j}(Q)`, where `u_i = ∂t_i/∂b`. This is
    the full content of charging merges for components joined plus
    `H_1(Sch(Q))`-image gained.
    - It proves `deep = law` on any level where it equals `law`. That
      happens on 33/200 random levels (`n = 5`, `j = 1`) and 24/150
      (`n = 4`, `j = 2`), all with `law = 1`.
    - Exact search found 0 violations.
  - *Where it dies.*
    - The chain rule `u_{j+1} = φ^j(u_1) u_j` bounds the certificate by
      `k_{u_1}(Q^{(j)})`, the depth-0 Fox annihilator of the transported
      level.
    - That is `o(n)` along every Farber tower in characteristic 0 (by
      Elek–Szabó and Linnell), and 0 on `p`-levels.
    - In characteristic `p` it is `o(n)` unless sofic Lück approximation
      fails for `u_1`.
    - Numerically, `B_j ≤ 2` up to `n = 400`, while `law_1 ≈ 0.114 n`.
    - So no field-coefficient homology count can give the weak form
      `deep ≥ c · law` on towers. Invariant: the Sylvester rank of `u_1`.
  - *Retract route (G), all levels.* By Hopficity, `K'` is never a retract or
    a free factor of `S`, or of any single-seed overfold hit, on any
    `L_j`-transitive level. This extends the w17-pull single-level kill.
    - The `H_1`-split part does not die universally.
      `det(H_1 K' → H_1 S) = ±1` on 3192/9504 `L_1`-transitive pairs at
      `n = 5`.
