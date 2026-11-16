# Changelog

Completed architectural and library changes, newest first. Detailed diffs remain
in Git; working statistics, build receipts and development plans are not kept here.

## 2026-11-15

- Removed duplicate and wrapper theorems (first pass of the theorem-by-theorem
  redundancy audit): 429 declarations whose content another theorem of the
  library already states (renamed or reparametrized copies, specializations
  with constants plugged in or an unused hypothesis, private/public twins,
  verbatim Mathlib re-exports). For each class the most general, best-placed
  statement is kept, under the clearer name; every call site, module header and
  Agda scaffold comment now uses it. No aliases are kept. Where a private lemma
  carried the proof of a public restatement, the public name now holds that
  proof; a few kept theorems were generalized to absorb their special cases
  (`GFL.LCLine.Params.contDiff_h`, `LimitedPI.mem_den_unstable_of_overload`,
  `PLL.pllHamiltonian_lie`, `PLL.ReducedSlow.mem_den_iff`). `Passive.Dq` uses
  `Transform.complexSymm` instead of its own copy of `[[a, −b], [b, a]]`.
  Classified theorems 7947 → 7518, public connection theorems 1144 → 1075.
  Removed public names and their replacements:
  - `Asymptotics.Guard.guardMFPT_committed_isBigO_atTop` → `Asymptotics.Guard.guardMFPT_committed_isBigO`
  - `Asymptotics.Guard.guardMFPT_committed_two_term_atTop` → `Asymptotics.Guard.guardMFPT_committed_two_term`
  - `Asymptotics.Guard.guardMFPT_guard_isBigO_atTop` → `Asymptotics.Guard.guardMFPT_guard_isBigO`
  - `Asymptotics.Guard.guardMFPT_ratio_isBigO_atTop` → `Asymptotics.Guard.guardMFPT_ratio_sub_two_isBigO`
  - `Asymptotics.Guard.guard_tail_cutoff_at_two` → `Asymptotics.Guard.guardPotential_scaled`
  - `Asymptotics.Guard.not_guardMFPT_guard_sub_one_isLittleO` → `Asymptotics.Guard.guardMFPT_guard_sub_one_isTheta`
  - `Asymptotics.Guard.not_guardMFPT_ratio_sub_two_isLittleO` → `Asymptotics.Guard.guardMFPT_ratio_sub_two_isTheta`
  - `Asymptotics.Guard.tendsto_guardMFPT_guard_mul_sqrt_atTop` → `Asymptotics.Guard.tendsto_guardMFPT_guard_sub_one_div_sqrt`
  - `Asymptotics.Guard.tendsto_guardMFPT_ratio_atTop` → `Asymptotics.Guard.tendsto_guardMFPT_ratio`
  - `Asymptotics.Guard.tendsto_guardMFPT_ratio_mul_sqrt_atTop` → `Asymptotics.Guard.tendsto_guardMFPT_ratio_sub_two_div_sqrt`
  - `Asymptotics.halfMoment1` → `Asymptotics.gaussMoment1`
  - `Asymptotics.halfMoment3` → `Asymptotics.gaussMoment3`
  - `Asymptotics.integral_mul_exp_neg_sq_div` → `Asymptotics.integral_mul_exp_neg_mul_sq_interval`
  - `Averaging.averaged_solves` → `Averaging.hasDerivAt_exp_mulVec`
  - `Averaging.hasDerivAt_slidingCoeff_of_ode` → `Averaging.hasDerivAt_slidingCoeff`
  - `Averaging.isHurwitz_iff_switched_decay` → `Averaging.switched_decay_of_isHurwitz`
  - `Criteria.charpoly_coeff_two_fin_three` → `Matrix.trace_eq_neg_charpoly_coeff`
  - `Criteria.charpoly_coeff_zero_fin_three` → `Matrix.det_eq_sign_charpoly_coeff`
  - `Criteria.det_characteristicMatrix_fin_four'` → `Criteria.det_characteristicMatrix_fin_four`
  - `Criteria.det_fin_two_of` → `Matrix.det_fin_two_of`
  - `Criteria.exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic` → `Criteria.exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic_violation`
  - `Criteria.exists_eigenvalue_re_pos_of_trace_pos_fin_four` → `Criteria.exists_eigenpair_re_pos_of_trace_pos`
  - `Criteria.exists_pos_real_eigenvector_of_det_pos_fin_three` → `Criteria.exists_pos_real_eigenvector_of_det`
  - `Criteria.exists_quartic_root_re_pos_of_cubic_coeff_neg` → `Criteria.exists_quartic_root_re_pos_of_violation`
  - `Criteria.holds_affine_of_det_characteristicMatrix_quartic` → `Criteria.holds_affine_iff_of_det_characteristicMatrix_quartic`
  - `Criteria.isHurwitz_fin_four_of` → `Criteria.isHurwitz_fin_four_iff`
  - `Criteria.isHurwitz_fin_three_iff_charpoly_coeff` → `Criteria.isHurwitz_fin_three_iff`
  - `Criteria.isHurwitz_fin_three_of` → `Criteria.isHurwitz_fin_three_iff`
  - `Criteria.isHurwitz_fin_two_of` → `Criteria.isHurwitz_fin_two_iff`
  - `Criteria.isHurwitz_of_det_characteristicMatrix_quartic` → `Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic`
  - `Criteria.quartic_hurwitz_iff_routh` → `Criteria.quartic_hurwitz_iff`
  - `Criteria.quartic_roots_re_neg_of_routh` → `Criteria.quartic_roots_re_neg_of`
  - `Criteria.spectrallyStable_fin_two_of_iff` → `Criteria.isHurwitz_fin_two_iff`
  - `Criteria.trace_det_eq_zero_ne_zero_iff_fin_two` → `Criteria.sq_eq_zero_iff_trace_det_eq_zero_fin_two`
  - `Criteria.trace_fin_two_of` → `Matrix.trace_fin_two_of`
  - `Criteria.unstable_of_jacobian_trace_pos_fin_four` → `Criteria.unstable_of_jacobian_violation_fin_four`
  - `CurrentControl.DigitalPI.isHurwitz_iff` → `CurrentControl.DigitalPI.mem_den_iff`
  - `CurrentControl.MismatchParams.isHurwitz_iff` → `CurrentControl.MismatchParams.mem_den_iff`
  - `CurrentControl.MismatchParams.residual_d` → `CurrentControl.residual_general`
  - `CurrentControl.PIParams.copied_det_characteristicMatrix` → `CurrentControl.PIParams.det_characteristicMatrix`
  - `CurrentControl.PIParams.lpf_isHurwitz_iff` → `CurrentControl.LPFLoop.lpfDen_eq`
  - `CurrentControl.PIParams.qLoop_mem_den_iff` → `CurrentControl.PIParams.refFeedback_mem_den_iff`
  - `CurrentControl.PIParams.refFeedback_isHurwitz_iff` → `CurrentControl.PIParams.refFeedback_mem_den_iff`
  - `CurrentControl.PIParams.withGain_det_characteristicMatrix` → `CurrentControl.PIParams.det_characteristicMatrix`
  - `CurrentControl.PIParams.withGain_mem_den_iff` → `CurrentControl.PIParams.mem_den_iff`
  - `CurrentControl.decoupling_power_cancel_out` → `CurrentControl.decoupling_power_cancel`
  - `CurrentControl.residual_caseA` → `CurrentControl.residual_general`
  - `CurrentControl.residual_caseB` → `CurrentControl.residual_general`
  - `CurrentControl.residual_general_q` → `CurrentControl.residual_general`
  - `CurrentControl.residual_rate` → `CurrentControl.residual_general`
  - `DAE.LinearDAE.isSolution_zero_iff` → `DAE.LinearDAE.isSolution_iff`
  - `DAE.Signature.pryce_le_pantelides` → `DAE.Signature.pryce_eq_pantelides`
  - `DAE.WeierstrassForm.isDiffIndex` → `DAE.WeierstrassForm.isDiffIndex_iff`
  - `DAE.isDiffIndex_blocks_iff` → `DAE.WeierstrassForm.isDiffIndex_iff`
  - `DAE.regular_iff_nonempty_weierstrassForm` → `DAE.weierstrass`
  - `Delay.norm_pureDelay_sub_pade11_le` → `Delay.norm_exp_neg_sub_pade11_le`
  - `Delay.norm_pureDelay_sub_pade22_le` → `Delay.norm_exp_neg_sub_pade22_le`
  - `Drives.InductionMachine.ifocFlux_detuned_globallyExponentiallyStable` → `Drives.InductionMachine.ifocFlux_globallyExponentiallyStable`
  - `Drives.InductionMachine.ifocFlux_tuned_globallyExponentiallyStable` → `Drives.InductionMachine.ifocFlux_globallyExponentiallyStable`
  - `Drives.PMSM.mtpa_on_circle` → `Drives.PMSM.mtpaIq_sq`
  - `Drives.Predictive.fcs_argmin_exists` → `Finset.exists_min_image`
  - `Dynamics.ForwardComplete.transport` → `Dynamics.forwardComplete_transport_iff`
  - `Dynamics.GlobalAsymptoticStable.transport` → `Dynamics.globalAsymptoticStable_transport_iff`
  - `Dynamics.GloballyAsymptoticallyStable.transport` → `Dynamics.holds_transport_iff`
  - `Dynamics.GloballyExponentiallyStable.transport` → `Dynamics.holds_transport_iff`
  - `Dynamics.LaSalle.isPositivelyInvariant_omegaLimitTraj` → `_root_.isPositivelyInvariant_omegaLimitTraj`
  - `Dynamics.LaSalle.lasalle_condition_of_trajectories` → `Dynamics.LaSalle.lasalle_condition_of_trajectories_mem`
  - `Dynamics.LaSalle.lasalle_global_asymptotic_stable` → `_root_.lasalle_global_asymptotic_stable`
  - `Dynamics.LaSalle.lasalle_invariance_principle` → `Dynamics.LaSalle.lasalle_invariance_principle_of_contDiff`
  - `Dynamics.LaSalle.lasalle_local_asymptotic_stable` → `_root_.lasalle_local_asymptotic_stable`
  - `Dynamics.LaSalle.lieDeriv_eq_zero_on_omegaLimitTraj` → `_root_.lieDeriv_eq_zero_on_omegaLimitTraj`
  - `Dynamics.LaSalle.mem_omegaLimitTraj_iff` → `_root_.mem_omegaLimitTraj_iff`
  - `Dynamics.LaSalle.regionOfAttraction_of_lasalle_lipschitz` → `Dynamics.LaSalle.regionOfAttraction_of_lasalle`
  - `Dynamics.LocalAsymptoticStable.transport` → `Dynamics.holds_transport_iff`
  - `Dynamics.LocallyExponentiallyStable.transport` → `Dynamics.holds_transport_iff`
  - `Dynamics.LyapunovStable.transport` → `Dynamics.holds_transport_iff`
  - `Dynamics.exists_pos_of_hasDerivAt` → `Dynamics.eventually_pos_of_hasDerivAt`
  - `Dynamics.forcedResponse_hasDerivAt` → `LinearSystems.ContinuousLinearSystem.isTrajectory_forcedResponse`
  - `Dynamics.forcedResponse_self` → `LinearSystems.variationOfConstants_self`
  - `Dynamics.forwardComplete_conjEquiv` → `Dynamics.forwardComplete_transport_iff`
  - `Dynamics.globallyAsymptoticallyStable_transport_iff` → `Dynamics.holds_transport_iff`
  - `Dynamics.globallyExponentiallyStable_transport_iff` → `Dynamics.holds_transport_iff`
  - `Dynamics.isEquilibrium_transport_iff` → `Dynamics.transportField_affineCoord_eq_zero_iff`
  - `Dynamics.isTrajectoryOn_of_eqOn` → `Dynamics.isIntegralCurveOn_of_eq_on_curve`
  - `Dynamics.lipschitzFlow_add` → `Flow.map_add`
  - `Dynamics.localAsymptoticStable_transport_iff` → `Dynamics.holds_transport_iff`
  - `Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_of_eqOn_ball` → `Dynamics.locallyExponentiallyStable_congr_nhds`
  - `Dynamics.locallyExponentiallyStable_transport_iff` → `Dynamics.holds_transport_iff`
  - `Dynamics.lyapunovStable_conjEquiv_iff` → `Dynamics.holds_conjEquiv_iff`
  - `Dynamics.lyapunovStable_transport_iff` → `Dynamics.holds_transport_iff`
  - `Dynamics.unstable_of_exponential_chetaev` → `NonlinearInstability.unstable_of_exponential_chetaev`
  - `Dynamics.unstable_of_jacobian_eigenvalue_re_pos_of_eqOn_ball` → `Dynamics.unstable_congr_nhds`
  - `Dynamics.unstable_transport_iff` → `Dynamics.holds_transport_iff`
  - `Envelope.den_safe_iInf` → `Envelope.holds_safe_iInf`
  - `Envelope.den_safe_sSup` → `Envelope.holds_safe_sSup`
  - `Envelope.le_sSup_certified_iff` → `Envelope.le_certifiedHorizon_iff`
  - `Estimation.LTV.stm_self` → `LinearSystems.stateTransitionMatrix_self`
  - `Estimation.bayes_cond` → `ProbabilityTheory.cond_eq_inv_mul_cond_mul`
  - `Estimation.importance_sampling_identity` → `MeasureTheory.Measure.setLIntegral_rnDeriv`
  - `Estimation.importance_sampling_identity_real` → `MeasureTheory.Measure.setIntegral_toReal_rnDeriv`
  - `Estimation.mc_strong_law` → `ProbabilityTheory.strong_law_ae`
  - `Estimation.posterior_ae_eq_withDensity` → `ProbabilityTheory.posterior_eq_withDensity`
  - `Estimation.posterior_comp_ae_eq` → `ProbabilityTheory.posterior_comp`
  - `Estimation.reversible_invariant` → `ProbabilityTheory.Kernel.IsReversible.invariant`
  - `Frequency.LFC.netEnergy_sub` → `Frequency.LFC.netEnergy_combo`
  - `Frequency.LFC.netXi_sub` → `Frequency.LFC.netXi_combo`
  - `Frequency.LFC.triangle_not_spectrallyStable` → `Frequency.LFC.triangle_not_mem_den_attractive`
  - `Frequency.SFR.isHurwitz_iff` → `Frequency.SFR.mem_den_attractive_iff`
  - `Frequency.SFR.isHurwitz_of_hp_fraction` → `Frequency.SFR.mem_den_globallyExponentiallyStable`
  - `Frequency.SFR.steadyState_isEquilibrium` → `Frequency.SFR.isEquilibrium_iff`
  - `Frequency.SwingGovernor.isHurwitz_iff` → `Frequency.SwingGovernor.mem_den_attractive_iff`
  - `Frequency.SwingGovernor.isHurwitz_iff_reduced` → `Frequency.SwingGovernor.mem_den_iff_reduce`
  - `Frequency.SwingGovernor.mem_den_globallyExponentiallyStable` → `Frequency.SwingGovernor.isHurwitz_iff_of_nonneg`
  - `Frequency.SwingGovernor.rateC_tCrit` → `Frequency.SwingGovernor.rateC_tCrit_add`
  - `Frequency.SwingGovernor.steadyState_isEquilibrium` → `Frequency.SwingGovernor.isEquilibrium_iff`
  - `GFL.DCLink.CarrierParams.carrierField_neg_eq_transport` → `GFL.DCLink.CarrierParams.carrierField_neg_sign_eq_transport`
  - `GFL.DCLink.CarrierParams.carrierField_reflect` → `GFL.DCLink.CarrierParams.carrierField_reflect_sign`
  - `GFL.DCLink.FourState.det_characteristicMatrix_A0_closed` → `GFL.DCLink.FourState.det_characteristicMatrix_A0`
  - `GFL.DCLink.FourStateBoundary.closedRouth_of_mem_den_locallyAsymptoticallyStable` → `GFL.DCLink.FourStateBoundary.closedRouth_of_mem_den_lyapunovStable`
  - `GFL.DCLink.ModelB.exactUnder_offBoundary_locallyAsymptoticallyStable` → `GFL.DCLink.ModelB.exactUnder_offBoundary`
  - `GFL.DCLink.ModelB.exactUnder_offBoundary_lyapunovStable` → `GFL.DCLink.ModelB.exactUnder_offBoundary`
  - `GFL.DCLink.ModelB.not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero` → `GFL.DCLink.ModelB.not_mem_den_locallyAsymptoticallyStable_of_Vdc_eq_zero`
  - `GFL.DCLink.ModelBParams.continuous_planeG` → `GFL.DCLink.ModelBParams.contDiff_planeG`
  - `GFL.DCLink.ModelBParams.continuous_planeH` → `GFL.DCLink.ModelBParams.contDiff_planeH`
  - `GFL.DCLink.closedLoop_mem_den_locallyExponentiallyStable` → `GFL.DCLink.closedLoop_mem_den_locallyExponentiallyStable_iff`
  - `GFL.DCLink.openLoop_mem_den_locallyExponentiallyStable` → `GFL.DCLink.openLoop_mem_den_locallyExponentiallyStable_iff`
  - `GFL.DCLink.pcc_eq_bridge_add_losses_si` → `Passive.SeriesRLC.dq_power_balance`
  - `GFL.LCLine.FormBParams.doubleAngle_coefficients_zero` → `GFL.LCLine.FormBParams.lineCurrent_rotational`
  - `GFL.LCLine.Params.contDiff_h_one` → `GFL.LCLine.Params.contDiff_h`
  - `GFL.LCLine.Params.current_part` → `GFL.LCLine.Params.sin_iQ_add_cos_iD`
  - `GFL.LCLine.Params.deriv_pllModel` → `GFL.LCLine.Params.deriv_h`
  - `GFL.LCLine.Params.field10_equilibria_eq` → `GFL.LCLine.Params.field10_eq_zero_iff`
  - `GFL.LCLine.Params.h_funext` → `GFL.LCLine.Params.h_eq_polar`
  - `GFL.LCLine.Params.reduced_energy_rate` → `GFL.LCLine.Params.energy_rate_with_drift`
  - `GFL.LCLine.Params.reduced_not_mem_den_lyapunovStable` → `GFL.LCLine.Params.reduced_mem_den_unstable`
  - `GFL.LCLine.code_mem_den_iff` → `GFL.LCLine.codeFamily_den`
  - `GFL.ModelLayers.DCParams.D1_currentOnly` → `GFL.ModelLayers.loopFactor_flip_current`
  - `GFL.ModelLayers.DCParams.fderiv_field_inConv` → `GFL.ModelLayers.DCParams.field_inConv`
  - `GFL.Noise.Embed.ito_freq_only` → `GFL.Noise.Embed.ito_emb`
  - `GFL.PowerLoop.QuasiStatic.exactUnder_locallyAsymptoticallyStable` → `GFL.PowerLoop.QuasiStatic.exactUnder_positiveGains`
  - `GFL.PowerLoop.QuasiStatic.exactUnder_lyapunovStable` → `GFL.PowerLoop.QuasiStatic.exactUnder_positiveGains`
  - `GFM.DroopVSM.localAsymptoticStable_iff` → `GFM.DroopVSM.den_eq_preimage`
  - `GFM.DroopVSM.locallyExponentiallyStable_iff` → `GFM.DroopVSM.den_eq_preimage`
  - `GFM.DroopVSM.lyapunovStable_iff` → `GFM.DroopVSM.den_eq_preimage`
  - `GFM.DroopVSM.unstable_iff` → `GFM.DroopVSM.den_eq_preimage`
  - `GFM.DroopVSM.vsm_mem_den_iff_swing` → `GFM.DroopVSM.vsm_mem_den_iff_swing_of_sinusoid`
  - `GFM.Matching.MatchingClosedLoop.mem_den_globallyAsymptoticallyStable` → `GFM.Matching.MatchingClosedLoop.mem_den_attractive`
  - `GFM.Matching.MatchingStiffGrid.mem_den_locallyAsymptoticallyStable` → `GFM.Matching.MatchingStiffGrid.mem_den_locallyAsymptoticallyStable_of_dissipative`
  - `GFM.VSMLPF.exists_equilibrium_iff_EVX` → `GFM.VSMLPF.exists_equilibrium_iff`
  - `GFM.hasDerivAt_powerAngle` → `GFM.VSMLPF.K_eq_deriv`
  - `Grid.withNetwork_sourceImpedance` → `Grid.networkModel_transfer`
  - `Implementation.mem_ofDesign` → `Implementation.certify_ofDesign`
  - `Information.boltzmann_pos` → `Information.gibbsVec_pos`
  - `Information.gibbs_isIProjection_own_moments` → `Information.gibbs_isIProjection`
  - `Information.sum_boltzmann` → `Information.sum_gibbsVec`
  - `Information.tiltedPath_maxCaliber` → `Information.klSum_gibbsVec_le`
  - `Limiting.dPriority_fst_of_abs_le` → `Limiting.clampSym_of_abs_le`
  - `Limiting.radialLimit_lipschitz` → `Limiting.radialLimit_dist_le`
  - `LinearAlgebra.lowerTriangular_mul` → `Matrix.BlockTriangular.mul`
  - `LinearAlgebra.rhs_perturbation` → `LinearAlgebra.matrix_perturbation`
  - `Map.holds_locallyExponentiallyStable` → `Map.locallyExponentiallyStable_of_schurStable`
  - `Map.holds_unstable` → `Map.unstable_of_inverse_schurStable`
  - `Modal.ModalBasis.bauerFike` → `Modal.bauerFike`
  - `Modal.ModalBasis.resolvent_diag` → `Modal.ModalBasis.resolvent_apply`
  - `Modal.ModalBasis.tendsto_pf_residue` → `Modal.ModalBasis.tendsto_resolvent_residue`
  - `Modal.bauerFike_normal_spectrum` → `Modal.bauerFike_normal`
  - `Modal.eigen_branch_deriv` → `Modal.eigen_branch_deriv_of_eventually`
  - `Modal.eigenvalue_deriv` → `Modal.eigenvalue_deriv_of_eventually`
  - `Modal.eigenvector_deriv` → `Modal.eigenvector_deriv_of_eventually`
  - `Modal.eigenvector_deriv_coeff` → `Modal.eigenvector_deriv_coeff_of_eventually`
  - `Modal.minimal_poles_eq_spectrum` → `Modal.minimal_pole_iff`
  - `Network.Swing.B_pos_of_weightOf_ne` → `Network.Swing.pos_of_mul_cos_ne`
  - `Network.Swing.angleMap_equilibrium` → `Network.Swing.angleMap_reduce`
  - `Network.Swing.equilibrium_wIdx` → `Network.Swing.reduce_wIdx`
  - `Network.Swing.ground_groupIndicator` → `Network.Swing.ground_sub_zero`
  - `Network.Swing.mem_den_locallyAsymptoticallyStable_iff_four` → `Network.Swing.mem_den_locallyAsymptoticallyStable_iff_four_machines`
  - `Network.Swing.not_exact_lyapunovStable_two` → `Network.Swing.not_exact_lyapunovStable`
  - `Network.Swing.sum_state` → `Fin.sum_univ_add`
  - `Network.Swing.uncoupled_mem_den_lyapunovStable` → `Network.Swing.uncoupledN_mem_den_lyapunovStable`
  - `Network.Swing.uncoupled_not_isHurwitz` → `Network.Swing.uncoupledN_not_isHurwitz`
  - `Network.Sync.card_components_eq_finrank_ker` → `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`
  - `Network.Sync.lapMatrix_mulVec_eq_zero_iff` → `SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable`
  - `Network.Sync.lapMatrix_mulVec_one` → `SimpleGraph.lapMatrix_mulVec_one_eq_zero`
  - `Network.Sync.lapMatrix_posSemidef` → `SimpleGraph.posSemidef_lapMatrix`
  - `Network.busFrequency_modal` → `Matrix.mulVec_sum`
  - `Network.busFrequency_sub_coi_commonMode` → `Network.busFrequency_commonMode`
  - `NormalForm.isTrajectoryOn_lift_iff` → `NormalForm.isIntegralCurveOn_lift_iff`
  - `Numerics.bdf2_index2_exact` → `Numerics.bdf_index2_exact`
  - `Numerics.daeJacobian_det` → `Matrix.det_fromBlocks₂₂`
  - `Numerics.euler_certified_small_step` → `Numerics.euler_sound_small_step_local`
  - `Numerics.euler_certified_small_step_local` → `Numerics.euler_sound_small_step_local`
  - `Numerics.euler_sound_small_step` → `Numerics.euler_sound_small_step_local`
  - `Numerics.forwardEuler_lte` → `Numerics.taylor_two_bound`
  - `Numerics.isHurwitz_of_trapezoidal_schurStable` → `Numerics.trapezoidal_schurStable_iff_isHurwitz`
  - `PDE.continuous_dtdt` → `PDE.continuous_second`
  - `PDE.continuous_dtdx` → `PDE.continuous_second`
  - `PDE.continuous_dxdx` → `PDE.continuous_second`
  - `PH.NonlinearModel.holds_passive` → `PH.NonlinearModel.passive_of_bddBelow`
  - `PH.NonlinearModel.passiveWith` → `PH.NonlinearModel.passiveWith_sub`
  - `PH.NonlinearModel.zeroInput_energy_antitone` → `PH.NonlinearModel.energy_antitoneOn_of_isIntegralCurveOn`
  - `PH.linear_system_eq_toPortHamiltonian` → `PH.linear_system_eq`
  - `PH.losslessLC_not_isHurwitz` → `PH.losslessLC_not_mem_den_locallyAsymptoticallyStable`
  - `PH.losslessLC_plant` → `PH.toPortHamiltonian_plant`
  - `PH.ofLp_ofDiagonal_field` → `PH.ofDiagonal_field`
  - `PLL.ReducedSlow.mem_den_globallyExponentiallyStable_iff` → `PLL.ReducedSlow.mem_den_iff`
  - `PLL.contDiff_trigPD` → `SpecialFunctions.contDiff_trigPoly2`
  - `PLL.ddsrf_decoupled` → `PLL.ddsrf_decoupling_error`
  - `PLL.ddsrf_positiveFrame_apply` → `PLL.ddsrf_positiveFrame`
  - `PLL.epsOd_eq` → `PLL.four_mul_zeta_sq`
  - `PLL.frequencyModel_bandwidth` → `PLL.normSq_closedLoopTF_eq_half_iff`
  - `PLL.hasDerivAt_trigPD` → `SpecialFunctions.hasDerivAt_trigPoly2`
  - `PLL.noiseProjection_sq_sum` → `PLL.StochasticPH.sigmaBare_dot_self`
  - `PLL.piPLLJacobian_exists_nonreal_eigenvalue_iff` → `PLL.piPLLJacobian_eigenvalues_real_iff`
  - `PLL.piPLLJacobian_zero_isNilpotent` → `PLL.piPLLJacobian_zero_sq`
  - `PLL.piPLL_isEquilibrium_iff` → `PLL.piPLLField_eq_zero_iff`
  - `PLL.pllHamiltonian_shifted_lie` → `PLL.pllHamiltonian_lie`
  - `PLL.pllPH_field` → `PLL.pllPH_field_input`
  - `PLL.pllPH_shifted_zeroInputField` → `PLL.pllPH_zeroInputField`
  - `PLL.srf_equilibria_eq` → `PLL.srfField_eq_zero_iff`
  - `PLL.srf_inPhase_jacobian_isHurwitz_iff` → `PLL.isHurwitz_linA_iff`
  - `PLL.standardTuning` → `PLL.rawVoltageTuning`
  - `PLL.xi_mem_den_locallyExponentiallyStable` → `PLL.srf_mem_den_locallyExponentiallyStable_inPhase`
  - `PLL.xi_mem_den_unstable_antiPhase` → `PLL.srf_mem_den_unstable_antiPhase`
  - `ParametricResonance.isTrajectoryOn_slowFlow_iff` → `ParametricResonance.isIntegralCurveOn_slowFlow_iff`
  - `ParametricResonance.slowFlow_exponentiallyStable_iff` → `ParametricResonance.slowFlow_holds_iff`
  - `Passive.DqRL.dqRL_of_alphaBetaRL` → `Passive.DqRL.alphaBetaRL_iff_dqRL`
  - `Passive.LCL.realize_routhHurwitz` → `Passive.LCL.stable_of_routhHurwitz`
  - `Passive.Line.Cable.det_ZY_of_Y2_zero` → `Passive.Line.Cable.det_ZY`
  - `Passive.Line.CableSchelkunoff.exactZin_div_surface_eq` → `Passive.Line.CableSchelkunoff.exactZin_eq_norm`
  - `Passive.Line.CableSchelkunoff.exactZout_div_surface_eq` → `Passive.Line.CableSchelkunoff.exactZout_eq_norm`
  - `Passive.Line.LosslessLine.bergeron_forward_through` → `Passive.Line.LosslessLine.bergeron_forward`
  - `Passive.Line.Phasor.cascade_relation` → `Matrix.mulVec_mulVec`
  - `Passive.Line.Telegrapher.second_order_i` → `Passive.Line.Telegrapher.second_order_v`
  - `Passive.RL.rl_inductance` → `Passive.RL.Impedance.inductance_ofParams`
  - `Passive.RL.rl_resistance` → `Passive.RL.Impedance.resistance_ofParams`
  - `Passive.seriesRLCPH_field` → `Passive.seriesRLC_field_eq_kirchhoff`
  - `Passive.seriesRLCPH_mem_den_globallyExponentiallyStable` → `Passive.seriesRLCPH_isHurwitz_iff`
  - `Periodic.hillGauge_conj` → `Periodic.hillMatrix_gauge_similar`
  - `Periodic.hillMatrix_det_eq` → `Periodic.hillMatrix_charpoly_eq`
  - `Potential.hasDerivAt_washboard` → `Potential.Barrier.hasDerivAt_washboard`
  - `Potential.washboard_kramers_prefactor` → `Potential.washboard_prefactor`
  - `Potential.washboard_shift` → `Potential.washboard_shift_int`
  - `SpecialFunctions.norm_gaussHalf` → `SpecialFunctions.norm_integral_gaussian_half`
  - `Spectral.meets_stable` → `Spectral.mem_realize_singleton`
  - `Spectral.meets_unstable` → `Spectral.mem_realize_singleton`
  - `Spectral.realize_univ_of` → `Spectral.realize_univ_eq_empty_of`
  - `Stochastic.BM.brownian_cov` → `ProbabilityTheory.IsPreBrownianReal.covariance_eval`
  - `Stochastic.BM.brownian_hasLaw` → `ProbabilityTheory.IsPreBrownianReal.hasLaw_eval`
  - `Stochastic.BM.brownian_increment_hasLaw` → `ProbabilityTheory.IsPreBrownianReal.hasLaw_sub`
  - `Stochastic.BM.brownian_indepIncrements` → `ProbabilityTheory.IsPreBrownianReal.hasIndepIncrements`
  - `Stochastic.BM.brownian_mean` → `ProbabilityTheory.IsPreBrownianReal.integral_eval`
  - `Stochastic.BM.brownian_scaling` → `ProbabilityTheory.IsBrownianReal.smul`
  - `Stochastic.BM.brownian_weakMarkov` → `ProbabilityTheory.IsPreBrownianReal.indepFun_shift`
  - `Stochastic.Conv.Lp_imp_inProbability` → `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`
  - `Stochastic.Conv.ae_imp_inProbability` → `MeasureTheory.tendstoInMeasure_of_tendsto_ae`
  - `Stochastic.Conv.inProbability_UI_imp_Lp` → `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`
  - `Stochastic.Conv.inProbability_imp_inDistribution` → `MeasureTheory.TendstoInMeasure.tendstoInDistribution`
  - `Stochastic.Conv.inProbability_subseq_ae` → `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`
  - `Stochastic.Conv.markov_inequality` → `MeasureTheory.mul_meas_ge_le_lintegral₀`
  - `Stochastic.Found.continuous_adapted_progressive` → `MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous`
  - `Stochastic.Found.discrete_adapted_progressive` → `MeasureTheory.StronglyAdapted.isStronglyProgressive_of_discrete`
  - `Stochastic.Found.law_eq_iff_fdd_eq` → `ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq`
  - `Stochastic.Found.law_eq_of_modification` → `ProbabilityTheory.map_eq_of_forall_ae_eq`
  - `Stochastic.Found.natural_adapted` → `MeasureTheory.Filtration.stronglyAdapted_natural`
  - `Stochastic.Found.predictable_adapted` → `MeasureTheory.IsStronglyPredictable.stronglyAdapted`
  - `Stochastic.Found.predictable_discrete_previsible` → `MeasureTheory.IsStronglyPredictable.measurable_add_one`
  - `Stochastic.Found.predictable_progressive` → `MeasureTheory.IsStronglyPredictable.isStronglyProgressive`
  - `Stochastic.Found.progressive_adapted` → `MeasureTheory.IsProgressive.adapted`
  - `Stochastic.Found.stronglyProgressive_stronglyAdapted` → `MeasureTheory.IsStronglyProgressive.stronglyAdapted`
  - `Stochastic.LDP.chernoff_bound` → `ProbabilityTheory.measure_ge_le_exp_mul_mgf`
  - `Stochastic.LDP.cramer_lower_bound_of_bounded` → `Stochastic.LDP.cramer_lower_bound_general`
  - `Stochastic.Markov.invariant_comp` → `ProbabilityTheory.Kernel.Invariant.comp`
  - `Stochastic.Markov.ionescuTulcea_marginal` → `ProbabilityTheory.Kernel.traj_map_frestrictLe`
  - `Stochastic.Markov.ionescuTulcea_next` → `ProbabilityTheory.Kernel.map_traj_succ_self`
  - `Stochastic.Markov.kernel_comp_assoc` → `ProbabilityTheory.Kernel.comp_assoc`
  - `Stochastic.Proc.continuous_exit_isStoppingTime` → `Stochastic.Proc.continuous_hitting_isStoppingTime`
  - `Stochastic.Proc.discrete_hitting_isStoppingTime` → `MeasureTheory.Adapted.isStoppingTime_hittingAfter`
  - `Stochastic.Proc.martingale_stoppedValue_condExp` → `MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_le_const`
  - `Stochastic.Proc.optional_stopping_bounded` → `MeasureTheory.Submartingale.expected_stoppedValue_mono`
  - `Stochastic.Proc.optional_stopping_iff` → `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`
  - `Stochastic.Proc.submartingale_stopped` → `MeasureTheory.Submartingale.stoppedProcess`
  - `Stochastic.QV.greedyQV_eq_sum` → `Stochastic.QV.qvSum_greedyPartition`
  - `Stochastic.SPH.itoDrift_eq_iff` → `add_eq_left`
  - `Stochastic.SPH.rlc_equipartition_two` → `Stochastic.SPH.rlc_equipartition`
  - `Synchronous.ClassicalSM.classicalSM_accel_fold` → `Synchronous.Swing.Pe_fold`
  - `Synchronous.ClassicalSM.den_flow_eq_preimage` → `Synchronous.ClassicalSM.mem_den_flow_iff_swing`
  - `Synchronous.ClassicalSM.mem_den_lyapunovStable` → `Synchronous.ClassicalSM.mem_den_lyapunovStable_iff`
  - `Synchronous.PostFaultSMIB.deltaS_lyapunovStable` → `Synchronous.Swing.deltaS_mem_den_lyapunovStable`
  - `Synchronous.SM.inv_diag_pos` → `Matrix.PosDef.diag_pos`
  - `Synchronous.SM.smIto_nonneg` → `Stochastic.SPH.itoCorrection_nonneg`
  - `Synchronous.Swing.Linearized.fderiv_point_eq_plant` → `Synchronous.Swing.Model.fderiv_point`
  - `Synchronous.Swing.Linearized.realize_univ` → `Synchronous.Swing.realize_univ`
  - `Synchronous.SwingParams.stateMatrix_mul` → `Synchronous.SwingParams.stateMatrix_eq_conj`
  - `Synchronous.smib11_Q_mulVec` → `Synchronous.smib11_dH`
  - `Synchronous.syncMachine7_Q_mulVec` → `Synchronous.syncMachine7_dH`
  - `Synchronous.syncMachine7_inv_posDef` → `Matrix.PosDef.inv`
  - `TMIO.Seed.gc₁` → `TMIO.gc_generate`
  - `TMIO.Seed.gc₂` → `TMIO.gc_generate`
  - `TMIO.Seed.gc₃` → `TMIO.gc_generate`
  - `TMIO.Seed.generate_uMO` → `TMIO.generate_comp`
  - `TMIO.Seed.generate_uTI` → `TMIO.generate_comp`
  - `TMIO.gc_image_core` → `TMIO.gc_generate`
  - `TMIO.generate_kern_apply` → `TMIO.generate_kern`
  - `TMIO.generate_preimage_apply` → `TMIO.generate_preimage`
  - `TMIO.le_map_sInf_setOf` → `TMIO.generate_isLeast`
  - `TMIO.sInfHom_monotone` → `OrderHomClass.mono`
  - `Transform.PerUnit.characteristicMatrix_puMatrix` → `Transform.Rebase.characteristicMatrix_rebaseMatrix`
  - `Transform.PerUnit.den_perUnit` → `Transform.Rebase.den_rebase`
  - `Transform.PerUnit.den_perUnit_timeScale` → `Transform.Rebase.den_rebase_timeScale`
  - `Transform.PerUnit.den_perUnit_unitTime` → `Transform.Rebase.den_rebase_timeScale`
  - `Transform.PerUnit.holds_puMatrix_iff` → `Transform.Rebase.holds_rebaseMatrix_iff`
  - `Transform.PerUnit.impedanceStable_perUnit_iff` → `Transform.Rebase.impedanceStable_rebase_iff`
  - `Transform.PerUnit.inertia_change_base` → `Transform.PerUnit.voltage_change_base`
  - `Transform.PerUnit.isHurwitz_closedLoop_perUnit_iff` → `Transform.Rebase.den_rebase`
  - `Transform.PerUnit.isHurwitz_puMatrix_iff` → `Transform.Rebase.spectrallyStable_rebaseMatrix_iff`
  - `Transform.PerUnit.power_change_base` → `Transform.PerUnit.voltage_change_base`
  - `Transform.PerUnit.returnDifference_perUnit` → `Transform.Rebase.returnDifference_rebase`
  - `Transform.PerUnit.solves_of_puMatrix` → `Transform.Rebase.solves_of_rebaseMatrix`
  - `Transform.PerUnit.solves_puMatrix_iff` → `Transform.Rebase.solves_rebaseMatrix_iff`
  - `Transform.PerUnit.solves_puMatrix_of` → `Transform.Rebase.solves_rebaseMatrix_of`
  - `Transform.PerUnit.spectrallyStable_puMatrix_iff` → `Transform.Rebase.spectrallyStable_rebaseMatrix_iff`
  - `Transform.PerUnit.transfer_puIO` → `Transform.Rebase.transfer_rebase`
  - `Transform.Rebase.den_rebase_unitTime` → `Transform.Rebase.den_rebase_timeScale`
  - `Transform.Rebase.holds_rebaseMatrix_one_iff` → `Transform.Rebase.holds_rebaseMatrix_timeScale_iff`
  - `Transform.Rebase.isHurwitz_closedLoop_rebase_iff` → `Transform.Rebase.den_rebase`
  - `Transform.Rebase.isHurwitz_rebaseMatrix_iff` → `Transform.Rebase.spectrallyStable_rebaseMatrix_iff`
  - `Transform.clarkePI_mem_orthogonalGroup` → `Transform.clarkePI_mul_transpose`
  - `Transform.complexPower_dq` → `Transform.complexPower_expand`
  - `Transform.complexSymm_eq_leftMulMatrix` → `Algebra.leftMulMatrix_complex`
  - `Transform.currentRef_export` → `Transform.currentRef_spec`
  - `Transform.det_park` → `Transform.det_rot`
  - `Transform.exportPower_dq` → `Transform.complexPower_expand`
  - `Transform.hasDerivAt_park_zero` → `Transform.hasDerivAt_park_mulVec`
  - `Transform.norm_park_mulVec` → `Transform.norm_rot_mulVec`
  - `Transform.park_add` → `Transform.rot_add`
  - `Transform.park_mulVec_J_mulVec` → `Transform.rot_mul_J`
  - `Transform.park_mulVec_sq_sum` → `Transform.frameRotation_power_invariant`
  - `Transform.park_mul_J` → `Transform.rot_mul_J`
  - `Transform.rot_mem_specialOrthogonalGroup` → `Transform.park_mem_specialOrthogonalGroup`
  - `Transform.rot_mulVec_J_mulVec` → `Transform.rot_mul_J`
  - `Transform.rot_mulVec_sq_sum` → `Transform.frameRotation_power_invariant`
  - `Transform.symCirc_mul_comm` → `Matrix.circulant_mul_comm`

- Second pass of the duplicate removal, over theorems whose call sites span several
  directories: 74 further declarations removed under the same rules. Some keepers
  moved to the more fundamental module (`Linear.mul_resolvent` and
  `Linear.spectrallyStable_smul_iff` into `Linear`), and `Delay.zoh_jω` now states
  the half-period-delay form. Classified theorems 7518 → 7444, public connection
  theorems 1075 → 1069. Removed public names and their replacements:
  - `Criteria.det_characteristicMatrix_fin_two'` → `Criteria.det_characteristicMatrix_fin_two`
  - `Criteria.isHurwitz_of_lyapunov` → `Criteria.re_neg_of_lyapunov`
  - `Criteria.spectrallyStable_fin_four_iff` → `Criteria.isHurwitz_fin_four_iff`
  - `Criteria.unstable_of_jacobian_quartic_const_neg` → `Criteria.unstable_of_jacobian_quartic_violation`
  - `CurrentControl.DigitalPI.pureDelay_τ_halves` → `Delay.pureDelay_three_half_periods`
  - `CurrentControl.DigitalPI.transfer_delay` → `Delay.transfer_pade11Model`
  - `CurrentControl.LoopDelay.norm_exp_neg_I_mul` → `Complex.norm_exp_ofReal_mul_I`
  - `DAE.det_complexify` → `RingHom.map_det`
  - `Delay.zoh_jω_eq_halfDelay` → `Delay.zoh_jω`
  - `Drives.InductionMachine.norm_sq_state2` → `PhasePlane.norm_sq_eq`
  - `Dynamics.conservative_conjEquiv` → `Linear.conservative_conj`
  - `Dynamics.decay_conjEquiv` → `Linear.decay_conj`
  - `Dynamics.hasDerivAt_of_coords` → `Dynamics.hasDerivAt_iff_coords`
  - `Dynamics.localAsymptoticStable_of_eqOn_ball` → `Dynamics.localAsymptoticStable_congr_nhds`
  - `Dynamics.lyapunovStable_conjEquiv` → `Linear.lyapunovStable_conj`
  - `Dynamics.lyapunovStable_of_eqOn_ball` → `Dynamics.lyapunovStable_congr_nhds`
  - `Dynamics.norm_le_abs_add_abs_three` → `Dynamics.norm_le_sum_abs`
  - `Dynamics.toEuclideanCLM_injective_fin_two` → `Matrix.toEuclideanCLM.injective`
  - `Estimation.predict_cov_ode_unique` → `Stochastic.Lyapunov.covODE_unique`
  - `Flow.QuadraticDecay.norm_bound` → `Flow.norm_bound_of_dissipation`
  - `GFL.DCLink.bridgePower_decoupling_cancel` → `CurrentControl.bridgePower_decoupling`
  - `GFL.Noise.Embed.embJ_skew` → `PH.transpose_symplectic_two`
  - `GFL.Noise.Embed.genL_emb_pH` → `Stochastic.SPH.genL_pH`
  - `GFL.Noise.classB_trace_div_det` → `PLL.piPLLJacobian_trace_det_relation`
  - `GFL.Parametric.PLLBlock.pll_closed_forms` → `PLL.det_characteristicMatrix_linA`
  - `GFM.DroopLPF.restoring_fold` → `Synchronous.Swing.Pe_fold`
  - `Grid.Interconnection.loadAdmittance_changeCoordinates` → `Linear.transfer_changeCoordinates`
  - `Grid.Interconnection.sourceImpedance_changeCoordinates` → `Linear.transfer_changeCoordinates`
  - `Grid.ModulationTransfer.Xeq_eq_parallel` → `Passive.SeriesRLC.parallel_inductors`
  - `Grid.withNetwork_returnDifference` → `Grid.networkModel_transfer`
  - `LTI.mul_self_fin_two` → `Criteria.sq_eq_trace_smul_sub_det_smul_fin_two`
  - `Linear.forall_eigen_smul_iff` → `Linear.forall_eigen_mobius_iff`
  - `Modal.ModalBasis.transfer_expansion` → `Modal.ModalBasis.io_expansion`
  - `Modal.ofRealVec_mulVec` → `RingHom.map_mulVec`
  - `Network.Swing.CycleMinimum.cos_base_pos` → `SpecialFunctions.sqrt_mul_cos_arcsin`
  - `Nonlinear.Polynomial2.norm_sq` → `PhasePlane.norm_sq_eq`
  - `NormalForm.BogdanovTakens.isNilpotent_ne_zero_iff_similar_jordanBlock` → `NormalForm.BogdanovTakens.trace_det_zero_iff_similar_jordanBlock`
  - `Numerics.EMT.rlMatrix_eq` → `Passive.RL.plant_A`
  - `Numerics.EMT.rlMatrix_isHurwitz_iff` → `Passive.RL.isHurwitz_iff`
  - `Numerics.portCoupled_isSolution_iff` → `DAE.LinearDAE.isSolution_iff`
  - `Numerics.pow_mulVec_eigen` → `Linear.mulVec_pow_of_eigen`
  - `PH.NonlinearModel.energy_antitoneOn_of_isTrajectoryOn` → `PH.NonlinearModel.energy_antitoneOn_of_isIntegralCurveOn`
  - `PH.phCx_mulVec_im` → `Modal.complexify_mulVec_im`
  - `PH.phCx_mulVec_re` → `Modal.complexify_mulVec_re`
  - `PLL.clarke_balancedAbc` → `Transform.clarke_mulVec_balanced`
  - `PLL.hasFDerivAt_coord_one` → `Dynamics.hasFDerivAt_coord`
  - `PLL.hasFDerivAt_coord_zero` → `Dynamics.hasFDerivAt_coord`
  - `PLL.hasFDerivAt_piPLLState_comp` → `Dynamics.hasFDerivAt_toEuclideanCLM_of_components`
  - `PLL.loopPoly_roots_re_neg_iff` → `Criteria.quadratic_roots_re_neg_iff`
  - `Passive.DqRL.isHurwitz_dqRLMatrix_iff` → `Passive.DqRL.spectrallyStable_dqRLMatrix_iff`
  - `Passive.LCL.realize_passive_damped` → `Passive.LCL.passive_stable_iff`
  - `Passive.Line.Cable.re_one_add_I_mul` → `SpecialFunctions.one_add_I_mul_re`
  - `PhasePlane.charRoot_iff` → `Criteria.det_characteristicMatrix_fin_two`
  - `SpecialFunctions.tendsto_besselNorm` → `SpecialFunctions.tendsto_bessel_div_gaussHalf`
  - `Spectral.not_root_of_isHurwitz` → `Linear.spectrallyStable_iff_isHurwitz`
  - `Spectral.sound_of_hub` → `Spectral.realize_subset_den_of_hub`
  - `Stack.subset_certified_iff` → `TMIO.Seed.gc_whole`
  - `Stochastic.Lyapunov.isHurwitz_transpose` → `Linear.isHurwitz_transpose_iff`
  - `Stochastic.NoiseFold.fold_barrier` → `NormalForm.Fold.barrier`
  - `Stochastic.SPH.skew_dotProduct_self` → `PH.dotProduct_mulVec_self_eq_zero_of_skew`
  - `TMIO.generate_cover_apply` → `TMIO.generate_cover`
  - `TMIO.generate_possibly_apply` → `TMIO.generate_possibly`
  - `Transform.Rebase.characteristicMatrix_conj'` → `Linear.characteristicMatrix_conj`
  - `Transform.Rebase.spectrallyStable_conj_iff` → `Linear.spectrallyStable_conj`
  - `Transform.Rebase.spectrallyStable_smul_iff` → `Linear.spectrallyStable_smul_iff`
  - `Transform.rot_mulVec_park_mulVec` → `Transform.rot_mul_park`
  - `Transform.rot_neg_mul_rot` → `Transform.park_mul_rot`
  - `Transform.svec_dot_cvec` → `Transform.cvec_dot_svec`

- Third pass, over the theorems with call sites in many files: 43 further
  declarations removed (37 public, 6 private twins merged into their public
  keeper); 49 were kept because their replacement would need more than a name
  change at many call sites, or because a test fixture, an Aesop rule or
  `Architecture.md` names them. `SpecialFunctions.arg_eq_arctan` now takes any `z`
  with `0 < z.re`; `Criteria.isHurwitz_fin_two_iff` and `isHurwitz_fin_three_iff` hold
  the proofs of the removed spectral forms. Entries of the lists above whose
  replacement was removed in this pass point at its final keeper. Classified
  theorems 7444 → 7401, public connection theorems 1069 → 1066. Removed public
  names and their replacements:
  - `Criteria.exists_characteristic_root_re_pos_of_trace_pos` → `Criteria.exists_root_re_pos_of_trace_pos`
  - `Criteria.exists_eigenvalue_re_pos_of_trace_pos` → `Criteria.exists_eigenpair_re_pos_of_trace_pos`
  - `Criteria.exists_eigenvalue_re_pos_of_trace_pos_fin_three` → `Criteria.exists_eigenpair_re_pos_of_trace_pos`
  - `Criteria.exists_pos_real_eigenvalue_of_det_neg` → `Criteria.exists_pos_real_eigenvalue_of_det`
  - `Criteria.exists_pos_real_eigenvector_of_det_neg` → `Criteria.exists_pos_real_eigenvector_of_det`
  - `Criteria.isHurwitz_iff_characteristic_roots` → `Linear.spectrallyStable_iff_isHurwitz`
  - `Criteria.isHurwitz_iff_charpoly_roots` → `Criteria.isHurwitz_iff_of_charpoly`
  - `Criteria.spectrallyStable_fin_three_iff` → `Criteria.isHurwitz_fin_three_iff`
  - `Criteria.spectrallyStable_fin_two_iff` → `Criteria.isHurwitz_fin_two_iff`
  - `Criteria.unstable_of_jacobian_det_neg_fin_four` → `Criteria.unstable_of_jacobian_violation_fin_four`
  - `CurrentControl.PIParams.isHurwitz_iff` → `CurrentControl.PIParams.mem_den_iff`
  - `Drives.InductionMachine.coordinate_smooth` → `Dynamics.contDiff_coord`
  - `Dynamics.LaSalle.lasalle_condition_of_lieDeriv` → `Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem`
  - `Dynamics.Mechanical.state_ext` → `Dynamics.state_ext_blocks`
  - `Dynamics.contDiff_of_components` → `contDiff_euclidean` (Mathlib)
  - `Dynamics.fderiv_eq_toEuclideanCLM_of_components` → `Dynamics.hasFDerivAt_toEuclideanCLM_of_components`
  - `Dynamics.fderiv_lift` → `Dynamics.hasFDerivAt_lift`
  - `Dynamics.isTrajectoryOn_transport` → `Dynamics.isIntegralCurveOn_transport`
  - `Dynamics.locallyExponentiallyStable_of_eqOn_ball` → `Dynamics.locallyExponentiallyStable_congr_nhds`
  - `Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian` → `hurwitz_linearization_locally_exponentially_stable` (LeanForControl)
  - `Dynamics.norm_le_abs_add_abs_two` → `Dynamics.norm_le_sum_abs`
  - `Dynamics.unstable_of_eqOn_ball` → `Dynamics.unstable_congr_nhds`
  - `Dynamics.unstable_of_jacobian_eigenvalue_re_pos` → `unstable_of_exists_complex_eigenvalue_re_pos` (LeanForControl)
  - `Flow.QuadraticDecay.energy_bound` → `Flow.energy_bound_of_dissipation`
  - `Flow.QuadraticDecay.holds` → `Flow.GloballyExponentiallyStable.holds`
  - `LTI.tendsto_equilibrium_apply` → `LTI.tendsto_apply_of_isHurwitz`
  - `Linear.det_characteristicMatrix` → `Linear.det_characteristicMatrix_eq_eval`
  - `Network.Swing.state_ext` → `Dynamics.state_ext_blocks`
  - `Nonlinear.Polynomial2.coordinate_smooth` → `Dynamics.contDiff_coord`
  - `Numerics.not_euler_realizationSoundUnder` → `Numerics.not_euler_realizationSoundUnder_local`
  - `PH.isHurwitz_of_dissipation_pos` → `PH.mem_den_globallyExponentiallyStable_of_dissipation_pos`
  - `ParametricResonance.det_characteristicMatrix_imag_ne_zero` → `Criteria.det_characteristicMatrix_ne_zero_of_isHurwitz`
  - `Passive.SeriesRLC.normSq_impedance_jω` → `Passive.SeriesRLC.norm_sq_impedance_jω`
  - `Port.System.autonomous_passive` → `Port.System.passive_of_noPorts`
  - `SingularPerturbation.hasDerivAt_mulVec` → `Dynamics.hasDerivAt_mulVec`
  - `Transform.Rebase.hasDerivAt_mulVec` → `Dynamics.hasDerivAt_mulVec`
  - `Transform.park_mulVec_rot_mulVec` → `Transform.park_mul_rot`

- Split bundled theorems into single-claim theorems (minimal-unit pass): 133
  theorems whose conclusion conjoined independent claims are replaced by 343
  named theorems, one claim each with its own docstring, or by theorems the
  library already had; bundles are removed without aliases and callers use the
  parts by name. Two closely tied parts are split only where a caller used one of
  them alone; criteria (`↔` with a list of parameter conditions) and conjunctions
  that share one existential witness stay whole. Some parts dropped hypotheses
  they do not use. Classified theorems 7401 → 7601 (public connection theorems
  1066 → 1074). Removed or narrowed bundles and their parts (names relative to
  the bundle's namespace unless qualified; a name listed among the parts now
  states only that part):
  - `Criteria.quadratic_partner` → `quadratic_partner_sum`, `quadratic_partner_prod`, `quadratic_partner` (root fact)
  - `Flow.quadratic_bounds` → `Flow.quadratic_lower_bound`, `Flow.quadratic_upper_bound`
  - `GFL.DCLink.ModelBParams.equilibrium_necessary` → `equilibrium_vgq`, `equilibrium_xpll` (`V_dc` part = existing `equilibrium_Vdc`)
  - `GFL.DCLink.ModelBParams.equilibrium_powerAngle` → `equilibrium_powerAngle`, `equilibrium_idRef`
  - `GFL.Noise.Params.varThetaQ_model` → existing `GFL.LCLine.Params.sigma_q_eq` and `GFL.Noise.varThetaQ_eq`
  - `GFM.Matching.MatchingClosedLoop.field_reduce` → `field_reduce`, `abField_load_stationary`
  - `LTI.sampledLoop_exponentialDecay` → `sampledLoop_exponentialDecay`, `sampledLoop_controller_exponentialDecay`
  - `NormalForm.exponentiallyStable_node_and_focus` → `exponentiallyStable_node`, `node_discriminant_pos`, `exponentiallyStable_focus`, `focus_discriminant_neg`
  - `NormalForm.Pitchfork.super_slopes` → `super_slope_zero`, `super_slope_sqrt`, `super_slope_neg_sqrt`
  - `Numerics.EMT.`{rlPlant,idealLCLPlant}_{trapezoidal,backwardEuler}`Discretization_exponentiallyStable` → …_wellPosed + …_exponentiallyStable
  - `Numerics.trapezoidal_real_multiplier_mem` → `trapezoidal_real_multiplier_gt_neg_one`, `trapezoidal_real_multiplier_neg`
  - `PhasePlane.Duffing.energy_off_well` → `energy_off_well`, `norm_mk_sub_mk_zero`
  - `Network.Swing.CycleMinimum.closure_sign` → `closure_neg_of_pos`, `closure_pos_of_neg`
  - `Network.Swing.norm_mul_cos_arg_sub` → `norm_mul_cos_arg_sub`, `norm_mul_sin_arg_sub`
  - `Network.Swing.Ring5.line_trig` → `line_cos`, `line_sin`; `line_trig'` → `line_cos'`, `line_sin'`
  - `Network.Swing.degenerate_addLeaf` → `powerBalance_addLeaf`, `strictMin_addLeaf`, `kernel_addLeaf`
  - `Synchronous.PostFaultSMIB.deltaS_stable_deltaU_unstable` → existing `Synchronous.Swing.deltaS_mem_den_locallyExponentiallyStable`, `deltaU_mem_den_unstable` (at m.toSwing)
  - `SingularPerturbation.LinearSP.coords_hasDerivAt` → `coords_hasDerivAt_slow`, `coords_hasDerivAt_fast`
  - `Stochastic.MFPT.kramersT_ode` → `kramersT_ode` (ODE identity only; others = existing `kramersT_hasDerivAt`, `outerG_hasDerivAt`)
  - `Transform.SpaceVector.inverterVector_active` → `inverterVector_100`, _110, _010, _011, _001, _101
  - `Criteria.quartic_routh_consequences` → `quartic_routh_a2_pos`, `quartic_routh_a1_lt`
  - `DAE.example_offsets` → `example_isTransversal`, `example_isDualFeasible`, `example_isTight`
  - `DAE.pendulum_offsets` → `pendulum_isTransversal`, `pendulum_isDualFeasible`, `pendulum_isTight`, `pendulum_noteIndex`, `pendulum_pryceIndex`
  - `Estimation.LTV.lti_cov_integral_form` → `lti_cov_self`, `hasDerivAt_lti_cov`, `lti_cov_unique`
  - `GFL.LCLine.Params.two_equilibria_per_period_den` → `stableRoot_mem_den_locallyExponentiallyStable`, `saddleRoot_mem_den_unstable`
  - `GFL.Parametric.Averages.fieldAngle_apply` → `fieldAngle_apply_zero`, `fieldAngle_apply_one`, `fieldAngle_apply_three`
  - `PLL.piPLL_jacobian_nilpotent_of_deriv_zero` → `piPLLField_eq_zero_iff`, `fderiv_piPLLField`, `piPLLJacobian_zero_ne_zero`, `piPLLJacobian_zero_sq`, `piPLLJacobian_zero_not_isHurwitz`
  - `Numerics.bdf_consistent` → `bdf1_consistent` … `bdf6_consistent`
  - `ParametricResonance.tongue_root_split` → `tongue_root_le`, `tongue_root_eq_iff`
  - `ParametricResonance.flipProjection_calpha_pos_lowGain` → `Ioo_subset_flipProjection_calpha_pos_lowGain`, `flipProjection_calpha_pos_lowGain_subset_Iio`
  - `Potential.doubleWell_curvatures` → `doubleWell_curvature_zero`, _sqrt, _neg_sqrt
  - `Potential.doubleWell_monotone` → `doubleWell_strictAntiOn_Iic`, `doubleWell_strictMonoOn_Icc_neg`, `doubleWell_strictAntiOn_Icc_pos`, `doubleWell_strictMonoOn_Ici`
  - `Potential.doubleWell_weight_bimodal` → `doubleWell_weight_strictMonoOn_Iic`, _strictAntiOn_Icc_neg, _strictMonoOn_Icc_pos, _strictAntiOn_Ici, `doubleWell_weight_max`, `doubleWell_weight_zero_lt`
  - `Frequency.LFC.netDiss_eq_zero` → `netXi_eq_zero_of_netDiss_eq_zero`, `netGap_mul_eq_zero_of_netDiss_eq_zero`
  - `Stochastic.Markov.semigroup_not_markov` → `unifKernel_comp`, `feller_transition`, `feller_not_markov`
  - narrowed (name kept, new siblings):
    - `DAE.Signature.pantelides_terminates` (+`pantelides_exists_final`)
    - `Dynamics.LaSalle.exists_globalization`
    - `lieDeriv_feedback_le` (+`output_eq_zero_of_lieDeriv_feedback_eq_zero`)
    - `GFL.LCLine.Params.fold_equilibrium_per_period` (+`fold_hZeros_eq`, `fold_reducedField_eq_zero`, `fold_jacobian_nilpotent`)
    - `reduced_jacobian_nilpotent`
    - `PLL.biased_fold` (+`biased_fold_eq_zero`)
    - `PLL.trigPLL_saddleNode_nilpotent`
    - `PLL.slowAngle_spec` (+`abs_slowAngle_lt`, `slowAngle_normal_neg`)
    - `Linear.eigen_mobius` (+`eigen_mobius_denom_ne_zero`)
    - `ScalarOscillator.forced_q_solves` (+`forced_q_eq_re`)
    - `upper_branch_le` (+`upper_branch_max`)
    - `flipProjection_calpha_pos_lowGain_isLUB` (+`deltaStarPlus_not_mem_…`)
    - `Periodic.hill3_neg_similar` (+`hill3_neg_charpoly_eq`, _spectrum_eq)
    - `exactHill_half_shift` (+…`charpoly_eq`, …`spectrum_eq`)
    - `Potential.anharmonicWell_unique_min` (+`anharmonicWell_critical_iff`)
    - `doubleWell_min` (+`doubleWell_eq_min_iff`)
    - `LinearSP.exists_epsStar_exponentiallyStable` (+`exists_epsStar_isHurwitz`)
  - `Asymptotics.Guard.guard_inside_bounds` → `guard_inside_ge`, `guard_inside_le`; `guard_ratio_bounds` → `guard_ratio_den_pos`, `guard_ratio_le`, `guard_ratio_ge`
  - `Averaging.exp_smul_bounds` → `norm_exp_smul_le_of_norm_le`, `norm_exp_smul_sub_one_le_of_norm_le`
  - `periodMap_schurStable_of_isHurwitz` (Schur part) + `periodMap_pow_norm_lt_one_of_isHurwitz`
  - `slowSwitching_counterexample` → `slowSwitching_isHurwitz₁`, _isHurwitz₂, _isHurwitz_avg, _periodMap_eigen, _not_schurStable
  - `Drives.Modulation.utilisation_bounds` → spwm/svpwm/`sixStep_utilisation_bounds`; `utilisation_values` → spwm/svpwm/`sixStep_utilisation_eq`
  - `Dynamics.Degenerate.exp_spiral_bounds` → `exp_spiral_ge`, `exp_spiral_le`
  - `Estimation.kalman_error_moments` → `kalman_error_memLp`, `kalman_error_integral_eq_zero`, `kalman_error_integral_sq`
  - `LTV.ltv_cov_stateTransition` → _self, `hasDerivAt_ltv_cov_stateTransition`, _unique
  - `GFL.DCLink.ModelB.boundaryWitnesses_mem_realize` → hopfCenter/hopfDamped/`cdcZero_mem_realize`; `boundaryWitnesses_not_mem_realize_offBoundary` → three …_not_mem_realize_offBoundary
  - `GFL.LCLine.Params.reduced_node_iff` → existing `Params.fderiv_reducedField`, `piPLLJacobian_eigenvalues_real_iff`
  - `GFL.RatePLL.imaginary_pair_at_boundary` → `trace_jac_eq_zero_of_tan_eq`, `det_jac_pos`, `imaginary_pair_at_boundary` (charpoly part)
  - `GFM.VSMLPF.gfmAngle_mixed_partial` → `gfmAngle_delta_partial`, `gfmAngle_mixed_partial` (u-derivative; args ωc K₀ u z), `gfmAngle_mixed_partial_ne_zero`
  - `PLL.pllHamiltonian_shifted_lyapunovFunction` → `pllHamiltonian_nonneg`, `pllHamiltonian_shifted_eq_zero`, `pllHamiltonian_shifted_lie_nonpos`
  - `Nonlinear.Polynomial2.quarticEnergy_bounds` → `quarticEnergy_le_norm_pow`, `norm_pow_le_two_mul_quarticEnergy`
  - `quartic_certificate_boundary` → `quartic_exponential`, `quarticModel_not_certified`
  - `Numerics.ggl_projection_vanishes` (Gᵀμ = 0) + `ggl_hasDerivAt_velocity`
  - `ParametricResonance.exp_victim_tuned` (+jω) + `exp_victim_tuned_conj`
  - `Passive.Line.Phasor.exp_two_mul_gammaL` (identity) + `one_sub_Zsc_div_Zc_ne_zero`
  - `Passive.Line.CableSchelkunoff.tendsto_norms` → `tendsto_besselI0Norm_mul`, _I1, _K0, _K1, `tendsto_cexp_neg_two_mul_sub`
  - `exactZ_tendsto_omega` → six exactZ…_tendsto_… lemmas
  - `besselNorm_sub_one_isBigO` → four bessel…`Norm_sub_one_isBigO`
  - `Periodic.transition_spec` → `transition_self`, `isIntegralCurveOn_transition`
  - `Frequency.FreqCov.swingCov_entries` → `swingCov_zero_one`, _one_zero, _one_one, _zero_zero
  - `SpecialFunctions.besselI0_div_besselI1_sub_one_le` (rate) + `besselI0_ne_zero_of_sector`, `besselI1_ne_zero_of_sector`
  - `besselK_laplace_le` → `besselK0_laplace_le`, `besselK1_laplace_le`
  - `tendsto_bessel_div_gaussHalf` → four `tendsto_bessel…_div_gaussHalf`
  - `Asymptotics.Guard.exp_tenth_bounds` → `exp_tenth_gt`, `exp_tenth_lt`
  - `exp_two_point_one_bounds` → `exp_two_point_one_gt`, `exp_two_point_one_lt`
  - `lifetime_ratio_num` → `lifetime_ratio_num_gt`, `lifetime_ratio_num_lt`, `lifetime_exp_factor_num_gt`
  - `Criteria.quadratic_root_re_im` → `quadratic_root_re`, `quadratic_root_im`
  - `eigen_ratio` (exact ratio) + `eigen_ratio_ge`, `eigen_ratio_le`
  - `eigen_bounds` → `eigen_fast_bounds`, `eigen_slow_bounds`
  - `Drives.DTC.sector_signs` → `sector_signs_add_one`, _add_two, _sub_one, _sub_two
  - `Dynamics.forwardSolution_spec` → `forwardSolution_zero`, `lipschitzFlow_solution`, `forwardSolution_unique`
  - `Estimation.predict_cov_hurwitz` → existing `Stochastic.Lyapunov.exists_solvesCovLyapunov`, `posSemidef_of_solvesCovLyapunov`, `solvesCovLyapunov_unique`, `covODE_unique`, `covSol_tendsto_norm`
  - `GFL.DCLink.CarrierParams.carrier_jacobian_charpoly` → `carrier_jacobian_conj` (charpoly = `Linear.charpoly_conj`); `equilibrium_Vdc` (`V_dc` = 1) + `equilibrium_idr`
  - `GFL.PowerLoop.QuasiStatic.hopfQS_c_apply` → `hopfQS_c1_apply`, _c2_apply, _c3_apply; `hopfQS_coords` → `hopfQS_z0_eq`, _z1_eq, _z2_eq
  - `GFM.Matching.MatchingStiffGrid.sq_le_energy_of_no_sync` → `sq_u_err_`/`sq_d_err_`/`sq_q_err_le_energy_of_no_sync`; `red_identity_aux` → `rot_iHat_eq`, `rot_iHat_deriv_eq`
  - `Modal.exists_eigenpair_branch_deriv` (existence) + `dotProduct_deriv_eq_zero_of_eventually`, `eigenvalue_deriv_left_of_eventually`
  - `NormalForm.riccatiGraze_escape` (bound on T) + `riccatiGraze_above`
  - `Frequency.SwingGovernor.arg_facts` → `arg_mk_pos`, `arg_mk_lt_pi`, `cos_arg_mk`, `norm_mk_pos`, `sq_norm_mk` (sine part: `Complex.sin_arg`)
  - `Stochastic.Conv.skorokhod_representation` (a.s. part; law parts = `aemeasurable_quantile`, `map_quantile`)
  - `Stochastic.Lyapunov.exists_unique_posSemidef_covLyapunov` → `posSemidef_of_solvesCovLyapunov` (+ `exists_solvesCovLyapunov`, `solvesCovLyapunov_unique`)
  - `exists_unique_posSemidef_stationaryCov` → `exists_stationaryCov`, `stationaryCov_posSemidef`
  - `cov_kernel_invariant` (Aᵀ-invariance) + `cov_kernel_transpose_eq_zero`
  - `stationaryCov_gramian` → existing `exists_stationaryCov`, `solvesCovLyapunov_unique`, `tendsto_integral_gramian`, `stationaryCov_posSemidef`, `posDef_iff_isControllable`
  - `Transform.PerUnit.transformer_pu` → `transformer_pu_voltage`, `transformer_pu_current`, `transformer_pu_impedance`

## 2026-11-08

- Reduced the passive elements to two dual topologies. `Passive.SeriesRLC`
  (`Passive/Series.lean`: `R`, `L`, elastance `S = 1/C`; impedance
  `R + Ls + S/s`) and `Passive.ParallelRLC` (`Passive/Parallel.lean`: `G`, `C`,
  reciprocal inductance `Γ = 1/L`; admittance `G + Cs + Γ/s`) replace
  `Passive.RL`, `Passive.GC` and `Passive.RX` (`Passive/Branch.lean`,
  `Passive/Shunt.lean`, `Passive/Phasor.lean` removed). RL, GC, pure L/C and the
  series RLC loop are the cases with some parameters zero; a phasor is the
  immittance at `s = jω` (`SeriesRLC.impedance_jω`, `reactance`, `absSq`).
  Models that need a first-order element state it with an explicit field
  (`S = 0` for series branches, `Γ = 0` for shunts): the RL impedance model, the
  dq branch, the current-loop plants, the GFL/GFM filters, lines and DC links,
  the SMIB11 link and terminal capacitor, the RL-network branches and nodes, the
  LCL and dq LC filters, the lossless line and the RLCG ladder. The quasi-static
  models' lines are series branches whose reactance is taken at the model's grid
  frequency (rate PLL `ω_s`, model B `ω_g`, VSG `ω_s`) or at the per-unit
  frequency `ω = 1` (quasi-static power loop, four-state, basin guard, post-fault
  SMIB). The power-flow line powers, the synchronous-machine line power and the
  current-limiting formulas take a series branch and a frequency; the form-B and
  stochastic-PH reactances are the reactances of the series branch
  `(R_g, L_g, C_f)`; the modulation-transfer reactances are series and parallel
  inductive branches. The dq immittances, per-unit laws, EMT companion elements
  and PH instances are stated for the two topologies.

## 2026-11-07

- Unified the remaining passive elements. Ideal inductors and capacitors are
  the lossless `Passive.RL`/`Passive.GC` (an explicit lossless field in the
  model): the DC links of the GFL models, the LCLine and form-B filter
  capacitors, the six-state carrier inductances, the SMIB11 terminal capacitor,
  the LCL and dq LC filters, the series RLC capacitor and the lossless line.
  Added the phasor branch `Passive.RX` (`Passive/Phasor.lean`: impedance,
  `|Z|²`, series and parallel connection, the reactances of `RL` and `GC`); the
  grid lines of the quasi-static models (rate PLL, quasi-static power loop, four-
  state, basin guard, model B, VSG) carry it, and the power-flow line powers,
  the synchronous-machine line power and the current-limiting formulas take
  it. The form-B and stochastic-PH line reactances are both built from the
  element reactances, and the modulation-transfer reactances are proved to be
  the series/parallel combinations. The DC-link PH instance is now the PH model
  of a `Passive.GC` (leakage `G ≥ 0`). The element per-unit laws moved from
  `Transform/PerUnit` to `Passive/PerUnit.lean` (the inductor law generalised to
  the RL branch), and the EMT companion elements are the RL branch and the GC
  shunt (companion formulas generalised to the lossy elements).
- The passive-component and grid-structure sources now declare in the
  namespaces of their directories: `Circuits.RL`/`Circuits.LCL` became
  `Passive.RL`/`Passive.LCL`, the dq RL branch `Passive.DqRL` (was
  `CurrentControl`), the PH instances `Passive` (was `PH.Models`), the lines
  `Passive.Line.*` (was `Line.*`); `Circuits.Interconnection` became
  `Grid.Interconnection`, and the RL networks, the grid impedance and the power
  flow declare in `Grid` (were `PH.Models`, `GFL.Impedance`, `Network`), the
  modulation transfer in `Grid.ModulationTransfer`. References in the library,
  tests, examples and Agda scaffolds follow. The KYP storage positivity of the
  RL model is now `Passive.RL.Impedance.energy_pos`, proved from the branch law.
- Separated passive components from grid structure. `Passive/` holds the
  components and their own properties (RL branch and its dq form, LCL filter,
  RLC and LC PH instances, lines and cables); `Grid/` holds how components are
  connected (source–load interconnection, RL networks, the grid impedance seen
  from a converter, power flow, shared network nodes). `Circuits/` is gone.
- Gave the series RL branch a single definition, `Passive.RL` (`Passive/Branch.lean`),
  with its decay rate, impedance, stored energy and power balance. The RL
  impedance model, the dq branch, the current-loop plants (PI, IMC, drive
  cascade), the GFL filters and lines, the GFM matching-control filters, the
  SMIB link, RL-network branches and the series RLC loop now carry a
  `Passive.RL` field; their former `R`/`L` names remain as accessors, and the
  restated sign-of-decay proofs now use `Passive.RL.decay_pos_iff`.
- Gathered the remaining simple R/L/C combinations into `Passive/`. Added the
  shunt `Passive.GC` (`Passive/Shunt.lean`, dual of `Passive.RL`) and the dq
  forms of both (`Passive/Dq.lean`: dq impedance and admittance matrices, the
  dq capacitor law moved from `Transform/Park`, and the dq power balance moved
  from `GFL/DCLink/PowerBalance`); both elements gained their trajectory energy
  balance. The GFL `Z_oc`/`Y_load` matrices are now the elements' dq
  immittances, and `Z_ext` moved to `Grid/GridImpedance`, which no longer
  depends on a GFL module. RL-network nodes, the GFM matching DC nodes and DC
  links, the closed-loop filter capacitor, the dq RL plant and impedance of
  `Passive/DqRL`, the RLCG ladder, the telegrapher equations and the line's
  characteristic impedance now carry `Passive.RL`/`Passive.GC`. Removed the
  restatements `dcEnergy_balance`, `pcc_eq_bridge_add_losses` and the duplicate
  dq impedance of `Passive/DqRL`; the IMC and drive-cascade decay proofs use
  `Passive.RL.decay_pos_iff`, the DC-droop one `Passive.GC.decay_pos_iff`.

## 2026-11-06

- Grouped the engineering sources by equipment class: `GridTiedConverter/` (`GFL`,
  `GFM` with current limiting under `GFM/Limiting`, `PLL`, `CurrentControl`),
  `PowerSystem/` (`Synchronous`, `Network`, `Frequency`), and `Circuits/Line`
  for lines and cables. Updated imports, scaffold module names and references
  while preserving public declaration namespaces.

- Consolidated the layer and implementation-interface documentation into
  `Architecture.md`, moved normative requirements into `Rules.md`, and removed
  the separate `Layers.md` and `ImplementationLayer.md` documents.
- Grouped Agda scaffolds by topic beside their Lean sources. Scaffold ownership
  now lives in source headers and is checked without a Markdown registry.
- Moved circuit PH instances to `Circuits/PH`, general family readings to
  `Family/Reading.lean`, symbolic resistance fitting to
  `Estimation/ResistanceFit.lean`, and formal tests to `tests/lean`.
  Updated imports while preserving public declaration namespaces.
- Completed TMIO classification of foundation and domain theorems
  (`ae37476`, `2ca127a`). Distinguished general coordinate theory from concrete
  electrical transformations and models, including Clarke/Park and dq (`4850810`).

## 2026-11-05

- Enforced incompatible TMIO and foundation/domain label combinations, while
  permitting M and TM with either class. Removed the automatic association of
  connection structure with domain metadata (`d34dd33`).
- Classified the remaining core theorems as foundation or domain (`0e1e9e9`).

## 2026-10-28–2026-10-30

- Established T and M nodes plus TM, MI and IO relations as the knowledge kinds;
  removed concrete observation records from the core (`7693ae3`).
- Stored classification directly on declarations with `@[tmio ...]` and removed
  duplicate maintained classification lists (`f7e37a9`, `232da3f`).
- Extended the closed connection grammar for polymorphic and constrained claims,
  migrated model results to certified connection interfaces, and completed their
  TMIO review. Added implicit EMT realization interfaces (`4ab6586`, `49c3d05`).

## 2026-10-26

- Added envelope sentences, random continuous-time behaviours and disturbed
  realizations, including the distinction between finite- and infinite-horizon
  safety (`bb46a37`).

## 2026-10-15–2026-10-21

- Introduced the model–implementation–record stack and the VSM platform interface,
  followed by current-loop mismatch, digital and voltage-limit realizations
  (`6368c01`, `a950849`, `18fe862`, `4741dfe`).
- Added discrete semantics, exact sampling, switched averaging and explicit Euler
  bridges, including systems with ports (`b730e23`, `2403c3e`, `dddf522`, `4ef99e1`).
- Shared family interpretation through generic spectral templates and hub readings;
  unified coordinate and base changes (`035d080`, `8316344`, `de6b8ba`).
- Added restatement checks and strengthened scaffold coverage, representation-change
  recognition and public-reference checks (`23deab3`, `825d15a`, `2f31b44`).

## 2026-10-11

- Established typed public connection claims and whole-package admission.
  Completed rational certificate synthesis and formalized certificate-language
  boundaries (`ffee892`, `af28db3`).
