import FiveOrgans.Memory
import FiveOrgans.Watcher
import FiveOrgans.Brake
import FiveOrgans.Viability
import FiveOrgans.BrakeDelay
import FiveOrgans.WatcherFallback
import FiveOrgans.Spotlight
import FiveOrgans.Skin
import FiveOrgans.TwoSpeed
import FiveOrgans.SpotlightNoisy
import FiveOrgans.BrakeDelay2
import FiveOrgans.WatcherCompliance
import FiveOrgans.BrakeDelayD
import FiveOrgans.BrakeDelayUnstable
import FiveOrgans.WatcherSpillover
import FiveOrgans.BrakeDelayEdge
import FiveOrgans.ViabilityStochastic
import FiveOrgans.Claims
import FiveOrgans.BrakeViability
import FiveOrgans.WatcherViability
import FiveOrgans.SkinViability
import FiveOrgans.TwoSpeedViability
import FiveOrgans.MemoryViability
import FiveOrgans.SpotlightViability
import FiveOrgans.JointViability
import FiveOrgans.WatcherDiscerning
import FiveOrgans.MemoryRandom
import FiveOrgans.FiveOrganAgent
import FiveOrgans.SkinSelective
import FiveOrgans.WatcherDiscernSpill
import FiveOrgans.CrossScale
import FiveOrgans.CrossScaleApprox
import FiveOrgans.CrossScaleHazard
import FiveOrgans.CrossScaleMarkov
import FiveOrgans.CrossScaleLongRun
import FiveOrgans.OpenWorld
import FiveOrgans.SpotlightEntropy
import FiveOrgans.SkinStochastic
import FiveOrgans.BrakeDelayExact
import FiveOrgans.BrakeDelayAtEdge
import FiveOrgans.JointCorrelated
import FiveOrgans.CrossScaleTest
import FiveOrgans.CrossScaleContract
import FiveOrgans.OrganCount
import FiveOrgans.BrakeWatcherLatency
import FiveOrgans.RowConcentration
import FiveOrgans.CrossScaleContrast
import FiveOrgans.DiffContrast
import FiveOrgans.MarkovOrder
import FiveOrgans.MarkovOrderK
import FiveOrgans.RandomCount
import FiveOrgans.FadingMemory
import FiveOrgans.BlockConcentration
import FiveOrgans.CanonicalAgent
import FiveOrgans.PoissonTail
import FiveOrgans.PoissonConf
import FiveOrgans.PoissonRandom
import FiveOrgans.PoissonFlip
import FiveOrgans.BernKL
import FiveOrgans.BennettDiff
import FiveOrgans.BennettRandom
import FiveOrgans.Ville
import FiveOrgans.Compression
import FiveOrgans.CompressionInfo
import FiveOrgans.CompressionCode
import FiveOrgans.VilleTwoArm
import FiveOrgans.UsefulCompression
import FiveOrgans.Coupled
import FiveOrgans.CoupledAblation
import FiveOrgans.CoupledTransfer
import FiveOrgans.CoupledRoles
import FiveOrgans.CoupledPartial
import FiveOrgans.CoupledStochastic
import FiveOrgans.CoupledEndogenous
import FiveOrgans.SensingRate
import FiveOrgans.ControlEntropy
import FiveOrgans.GrowthValue
import FiveOrgans.KnownStart
import FiveOrgans.Scrambling
import FiveOrgans.DataRate

open FiveOrgans

#print axioms Memory.separates
#print axioms Memory.memoryless_fails
#print axioms Memory.adequate_iff
#print axioms Memory.card_le_of_pairwise
#print axioms Memory.card_le_two_pow
#print axioms Watcher.helps_iff
#print axioms Watcher.helps_iff_threshold
#print axioms Watcher.sham_hurts
#print axioms Watcher.forced_check_formula
#print axioms Watcher.forced_check_tendsto
#print axioms Brake.bounded_of_window
#print axioms Brake.unbounded_of_outside
#print axioms Brake.window_iff
#print axioms Viability.stays_viable
#print axioms Viability.myopic_prefers_exploit
#print axioms Viability.sustain_beats_exploit
#print axioms Viability.sustain_invariant
#print axioms BrakeDelay.E_succ
#print axioms BrakeDelay.delayed_bounded
#print axioms BrakeDelay.delayed_unbounded
#print axioms BrakeDelay.delay_shrinks_window
#print axioms WatcherFallback.fallback_helps_iff
#print axioms WatcherFallback.flip_special_case
#print axioms WatcherFallback.independent_helps_iff
#print axioms WatcherFallback.always_flag_constant
#print axioms WatcherFallback.sham_fallback_hurts
#print axioms Spotlight.payoff_le
#print axioms Spotlight.spot_optimal
#print axioms Spotlight.spot_beats_uniform
#print axioms Spotlight.misdirected_spotlight
#print axioms Skin.skin_invariant
#print axioms Skin.skin_breach
#print axioms Skin.skin_window
#print axioms TwoSpeed.ema_diff
#print axioms TwoSpeed.step_error
#print axioms TwoSpeed.alt_amplitude
#print axioms TwoSpeed.single_rate_conflict
#print axioms TwoSpeed.two_rates_suffice
#print axioms TwoSpeed.conflict_instance
#print axioms SpotlightNoisy.noisy_pick_regret
#print axioms SpotlightNoisy.noisy_spot_near_optimal
#print axioms SpotlightNoisy.noisy_spot_beats_uniform
#print axioms SpotlightNoisy.noisy_spot_can_lose
#print axioms BrakeDelay2.E_formula
#print axioms BrakeDelay2.root_exists
#print axioms BrakeDelay2.b_gt_one
#print axioms BrakeDelay2.delay2_unbounded
#print axioms BrakeDelay2.delay2_shrinks_window
#print axioms BrakeDelay2.delay2_instance
#print axioms BrakeDelay2.root_stable
#print axioms BrakeDelay2.Eg_formula
#print axioms BrakeDelay2.delay2_bounded
#print axioms WatcherCompliance.gainQ_eq
#print axioms WatcherCompliance.perfect_watcher_gain
#print axioms WatcherCompliance.ignored_watcher_useless
#print axioms WatcherCompliance.gain_monotone_in_q
#print axioms BrakeDelay2.root_small
#print axioms BrakeDelay2.delay2_bounded_small
#print axioms BrakeDelay2.delay2_window
#print axioms BrakeDelayD.root_d
#print axioms BrakeDelayD.tele_bound
#print axioms BrakeDelayD.delayD_bounded_small
#print axioms BrakeDelayD.delay1_bounded_small
#print axioms BrakeDelayUnstable.big_root
#print axioms BrakeDelayUnstable.delayD_unbounded
#print axioms BrakeDelayUnstable.nodelay_bounded
#print axioms BrakeDelayUnstable.delay_caps_gain
#print axioms BrakeDelayUnstable.eq_dx
#print axioms BrakeDelayUnstable.delay1_window
#print axioms WatcherSpillover.gainQS_eq
#print axioms WatcherSpillover.no_spill_is_compliance
#print axioms WatcherSpillover.perfect_watcher_spill
#print axioms WatcherSpillover.adversarial_watcher
#print axioms WatcherSpillover.adversarial_full_defer
#print axioms BrakeDelayEdge.edge_rec
#print axioms BrakeDelayEdge.edge_no_decay
#print axioms BrakeDelayEdge.edge_pos
#print axioms BrakeDelayEdge.edge_le_one
#print axioms BrakeDelayEdge.edge_strict_anti
#print axioms BrakeDelayEdge.edge_one
#print axioms BrakeDelayEdge.edge_two
#print axioms ViabilityStochastic.surv_mem
#print axioms ViabilityStochastic.surv_ge
#print axioms ViabilityStochastic.budget_viable
#print axioms ViabilityStochastic.uniform_split
#print axioms ViabilityStochastic.const_hazard_dies
#print axioms ViabilityStochastic.geometric_viable
#print axioms ViabilityStochastic.surv_le_exp
#print axioms ViabilityStochastic.viable_bounded_hazard
#print axioms Claims.absence_fails
#print axioms Claims.misconfigured_worse_than_absent
#print axioms BrakeViability.geom_le
#print axioms BrakeViability.brake_in_window_viable
#print axioms BrakeViability.surv_le_pow
#print axioms BrakeViability.brake_out_of_window_dies
#print axioms WatcherViability.watcher_lowers_hazard
#print axioms WatcherViability.watcher_improves_survival
#print axioms WatcherViability.watcher_strictly_improves
#print axioms WatcherViability.static_watcher_still_dies
#print axioms WatcherViability.learning_watcher_viable
#print axioms WatcherViability.instance_watcher
#print axioms SkinViability.skin_in_window_safe
#print axioms SkinViability.steady_push_above
#print axioms SkinViability.skin_out_of_window_dies
#print axioms TwoSpeedViability.single_rate_dies
#print axioms TwoSpeedViability.two_rates_survive
#print axioms TwoSpeedViability.two_speed_instance
#print axioms MemoryViability.memoryless_trap
#print axioms MemoryViability.memoryless_dies
#print axioms MemoryViability.memory_survives
#print axioms MemoryViability.memory_instance
#print axioms SpotlightViability.meets_survives
#print axioms SpotlightViability.short_dies
#print axioms SpotlightViability.spot_survives_if_any
#print axioms SpotlightViability.demanding_world
#print axioms SpotlightViability.misdirected_world
#print axioms SpotlightViability.spotlight_instance
#print axioms JointViability.joint_eq_steps
#print axioms JointViability.joint_le
#print axioms JointViability.joint_needs_each
#print axioms JointViability.one_out_kills
#print axioms JointViability.all_in_budget
#print axioms JointViability.joint_instance
#print axioms WatcherDiscerning.gain2_eq
#print axioms WatcherDiscerning.constant_q
#print axioms WatcherDiscerning.undiscerning_sham_hurts
#print axioms WatcherDiscerning.discerning_never_hurts
#print axioms WatcherDiscerning.helps_iff_discernment
#print axioms WatcherDiscerning.adversarial_discerning
#print axioms WatcherDiscerning.adversarial_harmless_iff
#print axioms WatcherDiscerning.v6_instance
#print axioms MemoryRandom.rhz_mem
#print axioms MemoryRandom.memoryless_rhz_ge
#print axioms MemoryRandom.surv_le_of_ge
#print axioms MemoryRandom.memoryless_rate
#print axioms MemoryRandom.memoryless_dies_random
#print axioms MemoryRandom.memory_safe_random
#print axioms MemoryRandom.random_instance
#print axioms FiveOrganAgent.agentHz_mem
#print axioms FiveOrganAgent.agent_budget
#print axioms FiveOrganAgent.agent_one_fails
#print axioms FiveOrganAgent.brake_budget
#print axioms FiveOrganAgent.brake_hz_ge
#print axioms FiveOrganAgent.skin_hz_zero
#print axioms FiveOrganAgent.two_speed_hz_zero
#print axioms FiveOrganAgent.memory_hz_zero
#print axioms FiveOrganAgent.spot_hz_zero
#print axioms FiveOrganAgent.five_organs_viable
#print axioms FiveOrganAgent.brake_failure_kills
#print axioms FiveOrganAgent.skin_failure_kills
#print axioms FiveOrganAgent.one_rate_kills
#print axioms FiveOrganAgent.memoryless_kills
#print axioms FiveOrganAgent.short_focus_kills
#print axioms FiveOrganAgent.five_organs_instance
#print axioms SkinSelective.traj2_eq
#print axioms SkinSelective.sel_invariant
#print axioms SkinSelective.sel_breach
#print axioms SkinSelective.leaky_window
#print axioms SkinSelective.window_mono
#print axioms SkinSelective.selective_beats_uniform
#print axioms SkinSelective.selective_instance
#print axioms WatcherDiscernSpill.acc3_eq
#print axioms WatcherDiscernSpill.acc3_no_spill
#print axioms WatcherDiscernSpill.spill_helps_iff
#print axioms WatcherDiscernSpill.adversarial_spill
#print axioms WatcherDiscernSpill.sham_helps_iff
#print axioms WatcherDiscernSpill.honest_spill
#print axioms WatcherDiscernSpill.spill_tradeoff
#print axioms WatcherDiscernSpill.v6_sham_instance
#print axioms WatcherDiscernSpill.v6_all_arms
#print axioms CrossScale.iterate_comm
#print axioms CrossScale.viable_transfer
#print axioms CrossScale.ablation_transfer
#print axioms CrossScale.ablation_kills_iff
#print axioms CrossScale.intact_transfer
#print axioms CrossScale.implements_comp
#print axioms CrossScale.orbit_realizes_anything
#print axioms CrossScale.behaviour_not_enough
#print axioms CrossScale.implements_instance
#print axioms CrossScaleApprox.approx_iterate
#print axioms CrossScaleApprox.geom_le
#print axioms CrossScaleApprox.approx_uniform
#print axioms CrossScaleApprox.robust_stay
#print axioms CrossScaleApprox.robust_leave
#print axioms CrossScaleApprox.robust_ablation
#print axioms CrossScaleApprox.edge_flip
#print axioms CrossScaleHazard.surv_diff
#print axioms CrossScaleHazard.hazard_transfer_stay
#print axioms CrossScaleHazard.hazard_transfer_kill
#print axioms CrossScaleHazard.finite_horizon
#print axioms CrossScaleHazard.constant_mismatch_flips
#print axioms CrossScaleHazard.summable_instance
#print axioms CrossScaleMarkov.lump_sum
#print axioms CrossScaleMarkov.sv_lump
#print axioms CrossScaleMarkov.ablation_lump
#print axioms CrossScaleMarkov.survival_factors
#print axioms CrossScaleMarkov.no_chain_of_split
#print axioms CrossScaleMarkov.split_instance
#print axioms CrossScaleMarkov.lump_instance
#print axioms CrossScaleMarkov.sv_nonneg
#print axioms CrossScaleMarkov.sv_le_one
#print axioms CrossScaleMarkov.sv_out
#print axioms CrossScaleMarkov.markov_hazard_lower
#print axioms CrossScaleMarkov.markov_hazard_upper
#print axioms CrossScaleMarkov.fiber_sum
#print axioms CrossScaleMarkov.sv_approx_lump
#print axioms CrossScaleLongRun.drift_unbounded
#print axioms CrossScaleLongRun.longrun_flip
#print axioms OpenWorld.open_world_incomplete
#print axioms OpenWorld.closed_world_complete
#print axioms OpenWorld.organ_not_universal
#print axioms SpotlightEntropy.gibbs_term
#print axioms SpotlightEntropy.Z_pos
#print axioms SpotlightEntropy.softmax_pos
#print axioms SpotlightEntropy.softmax_sum
#print axioms SpotlightEntropy.log_softmax
#print axioms SpotlightEntropy.softmax_optimal
#print axioms SpotlightEntropy.entropy_le_log
#print axioms SpotlightEntropy.softmax_payoff_ge
#print axioms SpotlightEntropy.softmax_spreads
#print axioms SpotlightEntropy.expected_regret
#print axioms SkinStochastic.skin_step_safe
#print axioms SkinStochastic.exit_le_tail
#print axioms SkinStochastic.exit_ge_push
#print axioms SkinStochastic.surv_anti
#print axioms SkinStochastic.tail_viable
#print axioms SkinStochastic.heavy_tail_dies
#print axioms BrakeDelayExact.polar_pow
#print axioms BrakeDelayExact.roots_inside
#print axioms BrakeDelayExact.eig_root
#print axioms BrakeDelayExact.specRad_lt
#print axioms BrakeDelayExact.exact_edge_stable
#print axioms BrakeDelayExact.unbounded_of_root
#print axioms BrakeDelayExact.param_root
#print axioms BrakeDelayExact.rho_gt
#print axioms BrakeDelayExact.kf_edge
#print axioms BrakeDelayExact.exact_edge_unstable
#print axioms BrakeDelayExact.exact_window
#print axioms BrakeDelayAtEdge.bps_step
#print axioms BrakeDelayAtEdge.unit_bound
#print axioms BrakeDelayAtEdge.sh_pow
#print axioms BrakeDelayAtEdge.aeval_lin
#print axioms BrakeDelayAtEdge.bps_of_roots_inside
#print axioms BrakeDelayAtEdge.lam_norm
#print axioms BrakeDelayAtEdge.lam_conj_norm
#print axioms BrakeDelayAtEdge.lam_root
#print axioms BrakeDelayAtEdge.lam_conj_root
#print axioms BrakeDelayAtEdge.lam_ne
#print axioms BrakeDelayAtEdge.sector_absurd
#print axioms BrakeDelayAtEdge.roots_edge
#print axioms BrakeDelayAtEdge.pC_monic
#print axioms BrakeDelayAtEdge.pC_ne
#print axioms BrakeDelayAtEdge.pC_eval
#print axioms BrakeDelayAtEdge.deriv_ne
#print axioms BrakeDelayAtEdge.count_le_one
#print axioms BrakeDelayAtEdge.roots_decomp
#print axioms BrakeDelayAtEdge.exact_edge_bounded
#print axioms BrakeDelayAtEdge.edge_bounded_window
#print axioms JointCorrelated.P_mono
#print axioms JointCorrelated.P_and_ge
#print axioms JointCorrelated.allAlive_succ
#print axioms JointCorrelated.joint_le_marg
#print axioms JointCorrelated.joint_ge
#print axioms JointCorrelated.corr_all_in_budget
#print axioms JointCorrelated.corr_needs_each
#print axioms JointCorrelated.corr_one_out_kills
#print axioms JointCorrelated.allAlive_two
#print axioms JointCorrelated.dependence_matters
#print axioms FiveOrgans.CrossScaleTest.blk_sum
#print axioms FiveOrgans.CrossScaleTest.blk_nonneg
#print axioms FiveOrgans.CrossScaleTest.blk_dist
#print axioms FiveOrgans.CrossScaleTest.defect_transfer
#print axioms FiveOrgans.CrossScaleTest.certified_transfer
#print axioms FiveOrgans.CrossScaleTest.spread_eq_defect
#print axioms FiveOrgans.CrossScaleTest.data_test
#print axioms FiveOrgans.CrossScaleTest.split_rejects
#print axioms FiveOrgans.CrossScaleTest.lumpable_defect_zero
#print axioms FiveOrgans.CrossScaleTest.split_refutes_lumpable
#print axioms FiveOrgans.CrossScaleContract.B_nonneg
#print axioms FiveOrgans.CrossScaleContract.sv_gap_rec
#print axioms FiveOrgans.CrossScaleContract.B_decay
#print axioms FiveOrgans.CrossScaleContract.B_decay_le
#print axioms FiveOrgans.CrossScaleContract.stayP_le_one
#print axioms FiveOrgans.CrossScaleContract.sv_gap_uniform
#print axioms FiveOrgans.CrossScaleContract.data_test_uniform
#print axioms FiveOrgans.CrossScaleContract.Pl_sv
#print axioms FiveOrgans.CrossScaleContract.Qs_sv
#print axioms FiveOrgans.CrossScaleContract.Pl_defect
#print axioms FiveOrgans.CrossScaleContract.no_uniform_without_exit
#print axioms FiveOrgans.OrganCount.cov_mem
#print axioms FiveOrgans.OrganCount.covered_survives
#print axioms FiveOrgans.OrganCount.uncovered_dies
#print axioms FiveOrgans.OrganCount.viable_covers_all
#print axioms FiveOrgans.OrganCount.single_purpose_count
#print axioms FiveOrgans.OrganCount.fewer_single_purpose_dies
#print axioms FiveOrgans.OrganCount.k_purpose_count
#print axioms FiveOrgans.OrganCount.five_demands_need_five
#print axioms FiveOrgans.OrganCount.generalist_survives
#print axioms FiveOrgans.BrakeWatcherLatency.θ_pos'
#print axioms FiveOrgans.BrakeWatcherLatency.θ_le_pi
#print axioms FiveOrgans.BrakeWatcherLatency.θ_strictAnti
#print axioms FiveOrgans.BrakeWatcherLatency.kEdge_strictAnti
#print axioms FiveOrgans.BrakeWatcherLatency.kEdge_le
#print axioms FiveOrgans.BrakeWatcherLatency.latency_destabilizes
#print axioms FiveOrgans.BrakeWatcherLatency.latency_gap
#print axioms FiveOrgans.BrakeWatcherLatency.latency_breaks_any_gain
#print axioms FiveOrgans.BrakeWatcherLatency.safe_gain_under_latency
#print axioms FiveOrgans.RowConcentration.l1_eq_two_pos
#print axioms FiveOrgans.RowConcentration.l1_witness
#print axioms FiveOrgans.RowConcentration.ind_eq_sum
#print axioms FiveOrgans.RowConcentration.ind_univ
#print axioms FiveOrgans.RowConcentration.ind_mem
#print axioms FiveOrgans.RowConcentration.emp_sum
#print axioms FiveOrgans.RowConcentration.emp_gain
#print axioms FiveOrgans.RowConcentration.mean_ind
#print axioms FiveOrgans.RowConcentration.subset_tail
#print axioms FiveOrgans.RowConcentration.l1_tail
#print axioms FiveOrgans.RowConcentration.rows_tail
#print axioms FiveOrgans.RowConcentration.delta_solves
#print axioms FiveOrgans.CrossScaleContrast.contrast_refutes
#print axioms FiveOrgans.CrossScaleContrast.set_tail
#print axioms FiveOrgans.CrossScaleContrast.t_solves
#print axioms FiveOrgans.DiffContrast.weighted_tail
#print axioms FiveOrgans.DiffContrast.weighted_abs_tail
#print axioms FiveOrgans.DiffContrast.wt_sq_sum
#print axioms FiveOrgans.DiffContrast.wt_centered
#print axioms FiveOrgans.DiffContrast.diff_tail
#print axioms FiveOrgans.DiffContrast.diff_t_solves
#print axioms FiveOrgans.DiffContrast.diff_refutes
#print axioms FiveOrgans.MarkovOrder.lift_blk
#print axioms FiveOrgans.MarkovOrder.lift_nonneg
#print axioms FiveOrgans.MarkovOrder.lift_rowsum
#print axioms FiveOrgans.MarkovOrder.markov_iff_lumpable
#print axioms FiveOrgans.MarkovOrder.sv_markov
#print axioms FiveOrgans.MarkovOrder.markov_check_refutes
#print axioms FiveOrgans.MarkovOrder.order2_of_order1
#print axioms FiveOrgans.MarkovOrder.lift_blk_eq
#print axioms FiveOrgans.MarkovOrder.mem_sv_split
#print axioms FiveOrgans.MarkovOrder.mem_not_markov
#print axioms FiveOrgans.MarkovOrderK.liftH_blk
#print axioms FiveOrgans.MarkovOrderK.order_iff_lumpable
#print axioms FiveOrgans.MarkovOrderK.sv_order
#print axioms FiveOrgans.MarkovOrderK.order_check_refutes
#print axioms FiveOrgans.MarkovOrderK.shift_inj
#print axioms FiveOrgans.MarkovOrderK.tail_shift
#print axioms FiveOrgans.MarkovOrderK.window_order_iff
#print axioms FiveOrgans.MarkovOrderK.window_sv
#print axioms FiveOrgans.RandomCount.random_index_le
#print axioms FiveOrgans.RandomCount.interleave_inj
#print axioms FiveOrgans.RandomCount.random_diff
#print axioms FiveOrgans.RandomCount.random_diff_alpha
#print axioms FiveOrgans.FadingMemory.liftH_nonneg
#print axioms FiveOrgans.FadingMemory.liftH_rowsum
#print axioms FiveOrgans.FadingMemory.liftH_defect_le
#print axioms FiveOrgans.FadingMemory.fading_sv
#print axioms FiveOrgans.FadingMemory.memory_var_bound
#print axioms FiveOrgans.FadingMemory.window_fading_sv
#print axioms FiveOrgans.FadingMemory.geometric_order
#print axioms FiveOrgans.BlockConcentration.blkErr_le
#print axioms FiveOrgans.BlockConcentration.defect_transfer_blk
#print axioms FiveOrgans.BlockConcentration.certified_transfer_blk
#print axioms FiveOrgans.BlockConcentration.data_test_blk
#print axioms FiveOrgans.BlockConcentration.split_rejects_blk
#print axioms FiveOrgans.BlockConcentration.split_refutes_lumpable_blk
#print axioms FiveOrgans.BlockConcentration.ind_map
#print axioms FiveOrgans.BlockConcentration.emp_map
#print axioms FiveOrgans.BlockConcentration.blk_tail
#print axioms FiveOrgans.BlockConcentration.blk_rows_random
#print axioms FiveOrgans.BlockConcentration.blk_delta_solves
#print axioms FiveOrgans.BlockConcentration.blk_rows_alpha
#print axioms FiveOrgans.CanonicalAgent.surv_merge
#print axioms FiveOrgans.CanonicalAgent.mergeHz_mem
#print axioms FiveOrgans.CanonicalAgent.le_mergeHz_left
#print axioms FiveOrgans.CanonicalAgent.le_mergeHz_right
#print axioms FiveOrgans.CanonicalAgent.watchHz_mem
#print axioms FiveOrgans.CanonicalAgent.watch_budget
#print axioms FiveOrgans.CanonicalAgent.canonical_viable
#print axioms FiveOrgans.CanonicalAgent.canon_skin_kills
#print axioms FiveOrgans.CanonicalAgent.memory_part_kills
#print axioms FiveOrgans.CanonicalAgent.memory_one_rate_kills
#print axioms FiveOrgans.CanonicalAgent.memory_memoryless_kills
#print axioms FiveOrgans.CanonicalAgent.canon_spot_kills
#print axioms FiveOrgans.CanonicalAgent.canon_brake_kills
#print axioms FiveOrgans.CanonicalAgent.static_watcher_kills
#print axioms FiveOrgans.CanonicalAgent.canonical_instance
#print axioms FiveOrgans.PoissonTail.exp_le_chord
#print axioms FiveOrgans.PoissonTail.integrable_exp
#print axioms FiveOrgans.PoissonTail.mgf_le
#print axioms FiveOrgans.PoissonTail.mgf_sum_le
#print axioms FiveOrgans.PoissonTail.upper_tail
#print axioms FiveOrgans.PoissonTail.lower_tail
#print axioms FiveOrgans.PoissonTail.upper_opt
#print axioms FiveOrgans.PoissonTail.lower_opt
#print axioms FiveOrgans.PoissonTail.poisKL_alpha
#print axioms FiveOrgans.PoissonTail.upper_alpha
#print axioms FiveOrgans.PoissonTail.lower_alpha
#print axioms FiveOrgans.PoissonTail.two_sided_alpha
#print axioms FiveOrgans.PoissonTail.poisKL_ge
#print axioms FiveOrgans.PoissonTail.beats_hoeffding
#print axioms FiveOrgans.PoissonConf.poisKL_eq
#print axioms FiveOrgans.PoissonConf.poisKL_cont
#print axioms FiveOrgans.PoissonConf.poisKL_zero
#print axioms FiveOrgans.PoissonConf.kl_upper
#print axioms FiveOrgans.PoissonConf.lower_zero
#print axioms FiveOrgans.PoissonConf.kl_lower
#print axioms FiveOrgans.PoissonConf.kl_conf
#print axioms FiveOrgans.PoissonConf.exp_neg_log
#print axioms FiveOrgans.PoissonConf.kl_conf_alpha
#print axioms FiveOrgans.PoissonConf.kl_two_sample
#print axioms FiveOrgans.PoissonConf.kl_two_sample_alpha
#print axioms FiveOrgans.PoissonRandom.kl_conf_random
#print axioms FiveOrgans.PoissonRandom.card_Icc_one
#print axioms FiveOrgans.PoissonRandom.pos_of_Icc
#print axioms FiveOrgans.PoissonRandom.kl_conf_random_alpha
#print axioms FiveOrgans.PoissonRandom.kl_two_sample_random
#print axioms FiveOrgans.PoissonRandom.kl_two_sample_random_alpha
#print axioms FiveOrgans.PoissonFlip.flip_measurable
#print axioms FiveOrgans.PoissonFlip.flip_indep
#print axioms FiveOrgans.PoissonFlip.flip_range
#print axioms FiveOrgans.PoissonFlip.flip_mean
#print axioms FiveOrgans.PoissonFlip.kl_two_sample_flip
#print axioms FiveOrgans.PoissonFlip.kl_two_sample_flip_alpha
#print axioms FiveOrgans.BernKL.mgf_le_bern
#print axioms FiveOrgans.BernKL.bern_pos
#print axioms FiveOrgans.BernKL.mgf_sum_bern
#print axioms FiveOrgans.BernKL.sum_range_mem
#print axioms FiveOrgans.BernKL.upper_tail_bern
#print axioms FiveOrgans.BernKL.binKL_symm
#print axioms FiveOrgans.BernKL.upper_opt_bern
#print axioms FiveOrgans.BernKL.binKL_one
#print axioms FiveOrgans.BernKL.upper_one_bern
#print axioms FiveOrgans.BernKL.binKL_cont
#print axioms FiveOrgans.BernKL.poisKL_le_binKL
#print axioms FiveOrgans.BernKL.kl_upper_bern
#print axioms FiveOrgans.BernKL.flip_avg
#print axioms FiveOrgans.BernKL.kl_lower_bern
#print axioms FiveOrgans.BernKL.kl_conf_bern
#print axioms FiveOrgans.BernKL.kl_conf_bern_alpha
#print axioms FiveOrgans.BernKL.kl_two_sample_bern
#print axioms FiveOrgans.BernKL.kl_two_sample_bern_alpha
#print axioms FiveOrgans.BernKL.kl_conf_bern_random
#print axioms FiveOrgans.BernKL.kl_two_sample_bern_random_alpha

-- BennettDiff
#print axioms FiveOrgans.BennettDiff.phi_nonneg
#print axioms FiveOrgans.BennettDiff.wtail
#print axioms FiveOrgans.BennettDiff.wtail_flip
#print axioms FiveOrgans.BennettDiff.scaled_tail
#print axioms FiveOrgans.BennettDiff.bennett_test
#print axioms FiveOrgans.BennettDiff.tw_stat
#print axioms FiveOrgans.BennettDiff.tw_sum
#print axioms FiveOrgans.BennettDiff.bennett_two_sample
#print axioms FiveOrgans.BennettDiff.wtail_bern
#print axioms FiveOrgans.BennettDiff.scaled_tail_bern
#print axioms FiveOrgans.BennettDiff.bern_diff_test
#print axioms FiveOrgans.BennettDiff.bern_diff_two_sample

-- BennettRandom
#print axioms FiveOrgans.BennettRandom.sum_range_two_mul
#print axioms FiveOrgans.BennettRandom.ew_stat
#print axioms FiveOrgans.BennettRandom.ew_sum
#print axioms FiveOrgans.BennettRandom.bern_diff_random
#print axioms FiveOrgans.BennettRandom.bern_diff_random_alpha

-- Ville
#print axioms FiveOrgans.Ville.mul_le_abs
#print axioms FiveOrgans.Ville.int_exp
#print axioms FiveOrgans.Ville.mgf_pos'
#print axioms FiveOrgans.Ville.g_nonneg
#print axioms FiveOrgans.Ville.g_le
#print axioms FiveOrgans.Ville.g_int
#print axioms FiveOrgans.Ville.g_integral
#print axioms FiveOrgans.Ville.tm_nonneg
#print axioms FiveOrgans.Ville.tm_int
#print axioms FiveOrgans.Ville.tm_eq
#print axioms FiveOrgans.Ville.meas_nat
#print axioms FiveOrgans.Ville.tm_sm
#print axioms FiveOrgans.Ville.tm_martingale
#print axioms FiveOrgans.Ville.ville
#print axioms FiveOrgans.Ville.bern_base_pos
#print axioms FiveOrgans.Ville.ville_bern
#print axioms FiveOrgans.Ville.ville_bern_grid
#print axioms FiveOrgans.Compression.decEquiv_equivalence
#print axioms FiveOrgans.Compression.factor_adequate
#print axioms FiveOrgans.Compression.safeSet_adequate
#print axioms FiveOrgans.Compression.adequate_transport
#print axioms FiveOrgans.Compression.covers_of_safe
#print axioms FiveOrgans.Compression.safe_of_covers
#print axioms FiveOrgans.Compression.adequate_fin_iff
#print axioms FiveOrgans.Compression.bits_iff
#print axioms FiveOrgans.Compression.pairwise_bound_loose
#print axioms FiveOrgans.Compression.seq_sufficient
#print axioms FiveOrgans.Compression.law_factors
#print axioms FiveOrgans.Compression.card_laws_le
#print axioms FiveOrgans.Compression.regret_le
#print axioms FiveOrgans.Compression.expected_regret_le
#print axioms FiveOrgans.Compression.merge_regret_ge
#print axioms FiveOrgans.Compression.approx_compression_survives
#print axioms FiveOrgans.Compression.forget_safe_iff
#print axioms FiveOrgans.Compression.forget_kills
#print axioms FiveOrgans.CompressionInfo.push_nonneg
#print axioms FiveOrgans.CompressionInfo.push_sum
#print axioms FiveOrgans.CompressionInfo.le_push
#print axioms FiveOrgans.CompressionInfo.ent_push_eq
#print axioms FiveOrgans.CompressionInfo.ent_factor_le
#print axioms FiveOrgans.CompressionInfo.ent_le_log_card
#print axioms FiveOrgans.CompressionInfo.safe_entropy_bound
#print axioms FiveOrgans.CompressionInfo.memory_ge_decision_entropy
#print axioms FiveOrgans.CompressionInfo.entropy_bound_tight
#print axioms FiveOrgans.CompressionInfo.seq_sufficient_pos
#print axioms FiveOrgans.CompressionInfo.law_sufficient
#print axioms FiveOrgans.CompressionInfo.law_posUpdatable
#print axioms FiveOrgans.CompressionInfo.law_minimal
#print axioms FiveOrgans.CompressionInfo.compression_budget
#print axioms FiveOrgans.CompressionInfo.summable_compression_viable
#print axioms FiveOrgans.CompressionInfo.useful_compression_task_relative
#print axioms FiveOrgans.CompressionCode.sum_le_one_of_nil
#print axioms FiveOrgans.CompressionCode.kraft
#print axioms FiveOrgans.CompressionCode.kraft_code
#print axioms FiveOrgans.CompressionCode.code_length_ge_entropy
#print axioms FiveOrgans.CompressionCode.push_mul_sum
#print axioms FiveOrgans.CompressionCode.safe_code_bound
#print axioms FiveOrgans.VilleTwoArm.dif_mem
#print axioms FiveOrgans.VilleTwoArm.dif_meas
#print axioms FiveOrgans.VilleTwoArm.int_unit
#print axioms FiveOrgans.VilleTwoArm.dif_mean
#print axioms FiveOrgans.VilleTwoArm.dif_indep
#print axioms FiveOrgans.VilleTwoArm.ville_two_arm
#print axioms FiveOrgans.VilleTwoArm.ville_two_arm_alpha
#print axioms FiveOrgans.UsefulCompression.useful_iff_viable
#print axioms FiveOrgans.UsefulCompression.useful_compression
#print axioms FiveOrgans.UsefulCompression.trivial_useful_iff
#print axioms FiveOrgans.UsefulCompression.useful_compression_full
#print axioms FiveOrgans.Coupled.xa_conv
#print axioms FiveOrgans.Coupled.xd_conv
#print axioms FiveOrgans.Coupled.xC_conv
#print axioms FiveOrgans.Coupled.hd_quarter
#print axioms FiveOrgans.Coupled.hd_one_three
#print axioms FiveOrgans.Coupled.hd_one_six
#print axioms FiveOrgans.Coupled.hd_one_abs_block
#print axioms FiveOrgans.Coupled.hd_one_abs_sum
#print axioms FiveOrgans.Coupled.h_B_delay
#print axioms FiveOrgans.Coupled.h_B_nodelay
#print axioms FiveOrgans.Coupled.h_nB_nodelay
#print axioms FiveOrgans.Coupled.h_nB_delay
#print axioms FiveOrgans.Coupled.sum_quarter
#print axioms FiveOrgans.Coupled.sum_threeq
#print axioms FiveOrgans.Coupled.sum_zero_pow
#print axioms FiveOrgans.Coupled.h_nonneg
#print axioms FiveOrgans.Coupled.h_anti
#print axioms FiveOrgans.Coupled.S_le
#print axioms FiveOrgans.Coupled.S_tendsto
#print axioms FiveOrgans.Coupled.sum_le_initial
#print axioms FiveOrgans.Coupled.sum_le_initial'
#print axioms FiveOrgans.Coupled.sfac_pos
#print axioms FiveOrgans.Coupled.L1_pos
#print axioms FiveOrgans.Coupled.abs_sub_le2
#print axioms FiveOrgans.Coupled.dr_le
#print axioms FiveOrgans.Coupled.card_window
#print axioms FiveOrgans.Coupled.drift_sum_le
#print axioms FiveOrgans.Coupled.traj_le
#print axioms FiveOrgans.Coupled.traj_const
#print axioms FiveOrgans.Coupled.exceed_const
#print axioms FiveOrgans.Coupled.exceed
#print axioms FiveOrgans.Coupled.unstable_exceed
#print axioms FiveOrgans.Coupled.stays_iff
#print axioms FiveOrgans.Coupled.resource_iff
#print axioms FiveOrgans.Coupled.viable_iff
#print axioms FiveOrgans.Coupled.lat_pos
#print axioms FiveOrgans.Coupled.Hs_eq
#print axioms FiveOrgans.Coupled.peak_eq
#print axioms FiveOrgans.Coupled.viable_closed
#print axioms FiveOrgans.Coupled.brake_necessary
#print axioms FiveOrgans.Coupled.watcher_redundant
#print axioms FiveOrgans.Coupled.cost_W
#print axioms FiveOrgans.Coupled.viable_drop_watcher
#print axioms FiveOrgans.Coupled.memory_harmful
#print axioms FiveOrgans.Coupled.memory_helps_noshift
#print axioms FiveOrgans.Coupled.Hs_le_L1
#print axioms FiveOrgans.Coupled.Hs_mono
#print axioms FiveOrgans.Coupled.watcher_helps
#print axioms FiveOrgans.Coupled.spotlight_helps
#print axioms FiveOrgans.Coupled.skin_helps
#print axioms FiveOrgans.Coupled.brake_harmful_nodelay
#print axioms FiveOrgans.CoupledAblation.mk_ok
#print axioms FiveOrgans.CoupledAblation.calm_table
#print axioms FiveOrgans.CoupledAblation.delay_table
#print axioms FiveOrgans.CoupledAblation.shiftFast_table
#print axioms FiveOrgans.CoupledAblation.shiftSlow_table
#print axioms FiveOrgans.CoupledAblation.deadbeatShift_table
#print axioms FiveOrgans.CoupledAblation.hostile_table
#print axioms FiveOrgans.CoupledAblation.poor_table
#print axioms FiveOrgans.CoupledAblation.complementary_MW
#print axioms FiveOrgans.CoupledAblation.substitutable_SP
#print axioms FiveOrgans.CoupledAblation.similar_not_same
#print axioms FiveOrgans.CoupledAblation.harmful_M_B
#print axioms FiveOrgans.CoupledAblation.not_monotone
#print axioms FiveOrgans.CoupledAblation.organ_necessity_relative
#print axioms FiveOrgans.CoupledAblation.brake_nec_suff
#print axioms FiveOrgans.CoupledAblation.resources_bind
#print axioms FiveOrgans.CoupledTransfer.xC_linear
#print axioms FiveOrgans.CoupledTransfer.xC_add
#print axioms FiveOrgans.CoupledTransfer.xC_err_le
#print axioms FiveOrgans.CoupledTransfer.macro_micro_gap
#print axioms FiveOrgans.CoupledTransfer.transfer_viable
#print axioms FiveOrgans.CoupledTransfer.transfer_failure
#print axioms FiveOrgans.CoupledTransfer.transfer_intervention
#print axioms FiveOrgans.CoupledRoles.calm_b
#print axioms FiveOrgans.CoupledRoles.delay_b
#print axioms FiveOrgans.CoupledRoles.shiftFast_b
#print axioms FiveOrgans.CoupledRoles.shiftSlow_b
#print axioms FiveOrgans.CoupledRoles.deadbeat_b
#print axioms FiveOrgans.CoupledRoles.hostile_b
#print axioms FiveOrgans.CoupledRoles.poor_b
#print axioms FiveOrgans.CoupledRoles.roles_calm
#print axioms FiveOrgans.CoupledRoles.roles_delay
#print axioms FiveOrgans.CoupledRoles.roles_shiftFast
#print axioms FiveOrgans.CoupledRoles.roles_shiftSlow
#print axioms FiveOrgans.CoupledRoles.roles_deadbeat
#print axioms FiveOrgans.CoupledRoles.roles_hostile
#print axioms FiveOrgans.CoupledRoles.roles_poor
#print axioms FiveOrgans.CoupledRoles.minimal_calm
#print axioms FiveOrgans.CoupledRoles.minimal_delay
#print axioms FiveOrgans.CoupledRoles.minimal_shiftFast
#print axioms FiveOrgans.CoupledRoles.minimal_shiftSlow
#print axioms FiveOrgans.CoupledRoles.minimal_deadbeat
#print axioms FiveOrgans.CoupledRoles.minimal_hostile
#print axioms FiveOrgans.CoupledRoles.minimal_poor
#print axioms FiveOrgans.CoupledRoles.no_capacity_always_necessary
#print axioms FiveOrgans.CoupledRoles.no_universal_minimum
#print axioms FiveOrgans.CoupledRoles.every_role_occurs
#print axioms FiveOrgans.CoupledRoles.role_flip
#print axioms FiveOrgans.CoupledPartial.unit_le
#print axioms FiveOrgans.CoupledPartial.partial_bound
#print axioms FiveOrgans.CoupledPartial.partial_viable
#print axioms FiveOrgans.CoupledPartial.resPath_adm
#print axioms FiveOrgans.CoupledPartial.res_theta
#print axioms FiveOrgans.CoupledPartial.res_mem
#print axioms FiveOrgans.CoupledPartial.res_traj
#print axioms FiveOrgans.CoupledPartial.partial_unstable
#print axioms FiveOrgans.CoupledPartial.adapt_exact
#print axioms FiveOrgans.CoupledPartial.no_adapt_without_watcher
#print axioms FiveOrgans.CoupledPartial.no_baseline_without_memory
#print axioms FiveOrgans.CoupledPartial.resist_iff
#print axioms FiveOrgans.CoupledPartial.brake_resistance_nodelay
#print axioms FiveOrgans.CoupledPartial.perturbed_loop
#print axioms FiveOrgans.CoupledStochastic.resp_reflect
#print axioms FiveOrgans.CoupledStochastic.sq_reflect
#print axioms FiveOrgans.CoupledStochastic.memLp_resp
#print axioms FiveOrgans.CoupledStochastic.var_resp_eq
#print axioms FiveOrgans.CoupledStochastic.var_resp
#print axioms FiveOrgans.CoupledStochastic.mean_resp
#print axioms FiveOrgans.CoupledStochastic.cheb_resp
#print axioms FiveOrgans.CoupledStochastic.xC_shock
#print axioms FiveOrgans.CoupledEndogenous.step_lower
#print axioms FiveOrgans.CoupledEndogenous.rate_impossible
#print axioms FiveOrgans.CoupledEndogenous.clip_abs
#print axioms FiveOrgans.CoupledEndogenous.rate_sufficient
#print axioms FiveOrgans.CoupledEndogenous.clipPath_is_path
#print axioms FiveOrgans.CoupledEndogenous.rate_iff
#print axioms FiveOrgans.CoupledEndogenous.rate_iff_exogenous
#print axioms FiveOrgans.CoupledEndogenous.regen_closed
#print axioms FiveOrgans.CoupledEndogenous.eventually_neg
#print axioms FiveOrgans.CoupledEndogenous.depletion_kills
#print axioms FiveOrgans.CoupledEndogenous.static_not_recursive
#print axioms FiveOrgans.CoupledEndogenous.exogenous_sustainable
#print axioms FiveOrgans.CoupledEndogenous.mode_zero
#print axioms FiveOrgans.CoupledEndogenous.mode_twice_zero
#print axioms FiveOrgans.CoupledEndogenous.alternate_two
#print axioms FiveOrgans.CoupledEndogenous.alternate_run
#print axioms FiveOrgans.CoupledEndogenous.alternate_unbounded
#print axioms FiveOrgans.CoupledEndogenous.run_zero_stays
#print axioms FiveOrgans.CoupledEndogenous.dwell_two_safe
#print axioms FiveOrgans.CoupledEndogenous.response_lower
#print axioms FiveOrgans.CoupledEndogenous.drift_sum_ge
#print axioms FiveOrgans.CoupledEndogenous.afford_impossible
#print axioms FiveOrgans.CoupledEndogenous.accel_impossible
#print axioms FiveOrgans.CoupledStochastic.h_zero
#print axioms FiveOrgans.CoupledStochastic.sum_sq_le
#print axioms FiveOrgans.CoupledStochastic.stable_fail_le
#print axioms FiveOrgans.CoupledStochastic.stable_horizon_le
#print axioms FiveOrgans.CoupledStochastic.hd1_cases
#print axioms FiveOrgans.CoupledStochastic.hd1_sq
#print axioms FiveOrgans.CoupledStochastic.hd1_sq_sum
#print axioms FiveOrgans.CoupledStochastic.nobrake_var_eq
#print axioms FiveOrgans.CoupledStochastic.nobrake_var_unbounded
#print axioms FiveOrgans.CoupledStochastic.worst_vs_average
#print axioms FiveOrgans.CoupledStochastic.sustainable_count
#print axioms FiveOrgans.SensingRate.exists_cell
#print axioms FiveOrgans.SensingRate.cell_spec
#print axioms FiveOrgans.SensingRate.cell_safe
#print axioms FiveOrgans.SensingRate.count_needed
#print axioms FiveOrgans.SensingRate.step_iff
#print axioms FiveOrgans.SensingRate.forever_iff
#print axioms FiveOrgans.SensingRate.messages_iff
#print axioms FiveOrgans.SensingRate.bits_forever_iff
#print axioms FiveOrgans.SensingRate.blind_dies
#print axioms FiveOrgans.SensingRate.sensor_error_iff
#print axioms FiveOrgans.SensingRate.critical_error
#print axioms FiveOrgans.ControlEntropy.ent_eq
#print axioms FiveOrgans.ControlEntropy.mC_nonneg
#print axioms FiveOrgans.ControlEntropy.J_zero
#print axioms FiveOrgans.ControlEntropy.J_eq
#print axioms FiveOrgans.ControlEntropy.cond_nonneg
#print axioms FiveOrgans.ControlEntropy.cond_sum
#print axioms FiveOrgans.ControlEntropy.cond_chain
#print axioms FiveOrgans.ControlEntropy.ent_mix_ge
#print axioms FiveOrgans.ControlEntropy.mC_sum
#print axioms FiveOrgans.ControlEntropy.closed_eq
#print axioms FiveOrgans.ControlEntropy.touchette_lloyd
#print axioms FiveOrgans.ControlEntropy.ent_nonneg
#print axioms FiveOrgans.ControlEntropy.img_nonneg
#print axioms FiveOrgans.ControlEntropy.img_sum
#print axioms FiveOrgans.ControlEntropy.openSet_bdd
#print axioms FiveOrgans.ControlEntropy.touchette_lloyd_sup
#print axioms FiveOrgans.ControlEntropy.mX_eq_mix
#print axioms FiveOrgans.ControlEntropy.mi_nonneg
#print axioms FiveOrgans.ControlEntropy.ent_le_entJ
#print axioms FiveOrgans.ControlEntropy.mi_le_log_card
#print axioms FiveOrgans.ControlEntropy.reduction_le_messages
#print axioms FiveOrgans.ControlEntropy.cnot_tight
#print axioms FiveOrgans.ControlEntropy.log_four
#print axioms FiveOrgans.ControlEntropy.same_state_fails
#print axioms FiveOrgans.GrowthValue.mi_eq
#print axioms FiveOrgans.GrowthValue.mix_mean
#print axioms FiveOrgans.GrowthValue.J_le_mC
#print axioms FiveOrgans.GrowthValue.J_le_mX
#print axioms FiveOrgans.GrowthValue.mix_dist
#print axioms FiveOrgans.GrowthValue.mix_survives
#print axioms FiveOrgans.GrowthValue.value_le_mi
#print axioms FiveOrgans.GrowthValue.mean_diag
#print axioms FiveOrgans.GrowthValue.kelly_blind
#print axioms FiveOrgans.GrowthValue.kelly_cue
#print axioms FiveOrgans.GrowthValue.kelly_value_eq
#print axioms FiveOrgans.GrowthValue.indiv_eq
#print axioms FiveOrgans.GrowthValue.indiv_value_le
#print axioms FiveOrgans.GrowthValue.log_eight
#print axioms FiveOrgans.GrowthValue.mi_Jxy
#print axioms FiveOrgans.GrowthValue.indiv_beats_mi
#print axioms FiveOrgans.SensingRate.vol_fat
#print axioms FiveOrgans.SensingRate.hist_congr
#print axioms FiveOrgans.SensingRate.reach_step
#print axioms FiveOrgans.SensingRate.grow
#print axioms FiveOrgans.SensingRate.known_start_iff
#print axioms FiveOrgans.Scrambling.st_succ
#print axioms FiveOrgans.Scrambling.st_one
#print axioms FiveOrgans.Scrambling.hist_clean
#print axioms FiveOrgans.Scrambling.first_scrambled_fatal
#print axioms FiveOrgans.Scrambling.scramble_iff
#print axioms FiveOrgans.Scrambling.wt_nonneg
#print axioms FiveOrgans.Scrambling.wt_sum
#print axioms FiveOrgans.Scrambling.wt_clean
#print axioms FiveOrgans.Scrambling.wt_first
#print axioms FiveOrgans.Scrambling.separation
#print axioms FiveOrgans.DataRate.len
#print axioms FiveOrgans.DataRate.diff
#print axioms FiveOrgans.DataRate.radius_lower
#print axioms FiveOrgans.DataRate.R_pos
#print axioms FiveOrgans.DataRate.zoom
#print axioms FiveOrgans.DataRate.stabilise_iff
