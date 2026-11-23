import SpectralTheorem

/-! Every main declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. -/

-- SpectralMeasure (M1)
#print axioms SpectralTheorem.integral_spectralMeasure
#print axioms SpectralTheorem.integral_norm_sq_spectralMeasure
#print axioms SpectralTheorem.spectralMeasure_univ
#print axioms SpectralTheorem.eq_spectralMeasure

-- MultiplicationBounded, MultiplicationUnbounded (M2)
#print axioms SpectralTheorem.adjoint_mulL
#print axioms SpectralTheorem.mulL_mul
#print axioms SpectralTheorem.tendsto_mulL_apply
#print axioms SpectralTheorem.adjoint_mulPMap
#print axioms SpectralTheorem.isSelfAdjoint_mulPMap
#print axioms SpectralTheorem.tendsto_mulL_apply_mulPMap

-- Cyclic (M3)
#print axioms SpectralTheorem.cyclicIsometry_toLp
#print axioms SpectralTheorem.range_cyclicIsometry
#print axioms SpectralTheorem.cyclicIsometry_smul
#print axioms SpectralTheorem.cyclicSubmodule_isOrtho

-- SigmaMeasure, SigmaL2, Decomposition, MultiplicationForm (M4)
#print axioms SpectralTheorem.lintegral_sigmaMeasure
#print axioms SpectralTheorem.sigmaL2Equiv_symm_ae_eq
#print axioms SpectralTheorem.CyclicDecomposition.nonempty
#print axioms SpectralTheorem.CyclicDecomposition.isHilbertSum
#print axioms SpectralTheorem.CyclicDecomposition.unitary_cfcHom
#print axioms SpectralTheorem.CyclicDecomposition.unitary_apply_T
#print axioms SpectralTheorem.exists_unitary_mulL

-- BoundedMeasurable, BorelCalculus, BorelCalculusProperties, SpectralProjection (M5)
#print axioms SpectralTheorem.mulHom
#print axioms SpectralTheorem.IsBorelCalculus.unique
#print axioms SpectralTheorem.existsUnique_isBorelCalculus
#print axioms SpectralTheorem.borelCalc_continuousMap
#print axioms SpectralTheorem.borelCalc_id
#print axioms SpectralTheorem.norm_borelCalc_le
#print axioms SpectralTheorem.tendsto_borelCalc_apply
#print axioms SpectralTheorem.borelCalc_eq_borelHom
#print axioms SpectralTheorem.borelCalc_apply_of_apply_eq_smul
#print axioms SpectralTheorem.borelCalc_nonneg
#print axioms SpectralTheorem.isPositive_borelCalc
#print axioms SpectralTheorem.commute_borelCalc_of_commute
#print axioms SpectralTheorem.commute_borelCalc_of_isSelfAdjoint
#print axioms SpectralTheorem.inner_borelCalc_eq_integral
#print axioms SpectralTheorem.isStarProjection_spectralProjection
#print axioms SpectralTheorem.spectralProjection_mul
#print axioms SpectralTheorem.spectralProjection_empty
#print axioms SpectralTheorem.spectralProjection_ball
#print axioms SpectralTheorem.tendsto_sum_spectralProjection
#print axioms SpectralTheorem.inner_spectralProjection

-- MonotoneClass (for M5), Resolvent (for M7)
#print axioms SpectralTheorem.IsBoundedLimitClosed.of_continuous
#print axioms SpectralTheorem.adjoint_resolventI
#print axioms SpectralTheorem.isStarNormal_resolventI

-- ResolventSpectrum, UnboundedMultiplicationForm, SeparableDecomposition (M7, M4)
#print axioms SpectralTheorem.normSq_add_im_eq_zero_of_mem_spectrum
#print axioms SpectralTheorem.spectralProjection_resolvent_zero
#print axioms SpectralTheorem.CyclicDecomposition.ae_coord_ne_zero
#print axioms SpectralTheorem.CyclicDecomposition.mem_domain_iff
#print axioms SpectralTheorem.CyclicDecomposition.unitary_apply_selfAdjoint
#print axioms SpectralTheorem.exists_unitary_mulPMap
#print axioms SpectralTheorem.CyclicDecomposition.countable_vectors
#print axioms SpectralTheorem.CyclicDecomposition.exists_isFiniteMeasure
#print axioms SpectralTheorem.exists_unitary_mulL_finite
#print axioms SpectralTheorem.exists_unitary_mulPMap_finite

-- UnboundedCalculus, UnboundedCalculusProperties, UnboundedCalculusUnique,
-- SelfAdjointCalculus (M8)
#print axioms SpectralTheorem.norm_selfAdjointCalc_le
#print axioms SpectralTheorem.tendsto_selfAdjointCalc_apply_self
#print axioms SpectralTheorem.tendsto_selfAdjointCalc_apply
#print axioms SpectralTheorem.selfAdjointCalc_apply
#print axioms SpectralTheorem.selfAdjointCalc_apply_of_eigen
#print axioms SpectralTheorem.isPositive_selfAdjointCalc
#print axioms SpectralTheorem.IsSelfAdjointCalculus.map_resolventFn
#print axioms SpectralTheorem.IsSelfAdjointCalculus.eq_selfAdjointCalc
#print axioms SpectralTheorem.isSelfAdjointCalculus_selfAdjointCalc
#print axioms SpectralTheorem.existsUnique_isSelfAdjointCalculus

-- ProjectionValuedMeasure, PVMIntegral (M6: p.v.m.'s, Theorem VII.7)
#print axioms SpectralTheorem.ProjectionValuedMeasure.mul_apply
#print axioms SpectralTheorem.ProjectionValuedMeasure.inner_apply_eq_measureReal
#print axioms SpectralTheorem.ProjectionValuedMeasure.measure_map
#print axioms SpectralTheorem.ProjectionValuedMeasure.inner_integral
#print axioms SpectralTheorem.ProjectionValuedMeasure.tendsto_integral_apply
#print axioms SpectralTheorem.ProjectionValuedMeasure.existsUnique_inner_integral
#print axioms SpectralTheorem.ProjectionValuedMeasure.eq_integral_of_indicator
#print axioms SpectralTheorem.ProjectionValuedMeasure.integral_map

-- SpectralPVM (M6: Theorem VII.8)
#print axioms SpectralTheorem.spectralPVM_integral
#print axioms SpectralTheorem.toOperator_spectralPVM
#print axioms SpectralTheorem.ProjectionValuedMeasure.spectralPVM_toOperator
#print axioms SpectralTheorem.ProjectionValuedMeasure.mem_spectrum_toOperator_iff
#print axioms SpectralTheorem.mem_spectrum_iff_spectralPVM_ball
#print axioms SpectralTheorem.isSelfAdjoint_iff_spectralPVM
#print axioms SpectralTheorem.spectralPVMEquiv
#print axioms SpectralTheorem.selfAdjointPVMEquiv

-- UnitaryConj, UnboundedBorel (M9: g(A) for unbounded Borel g)
#print axioms SpectralTheorem.adjoint_unitaryConj
#print axioms SpectralTheorem.inner_selfAdjointCalc
#print axioms SpectralTheorem.mem_borelPMap_domain
#print axioms SpectralTheorem.inner_borelPMap
#print axioms SpectralTheorem.eq_borelPMap_of_inner
#print axioms SpectralTheorem.adjoint_borelPMap
#print axioms SpectralTheorem.isSelfAdjoint_borelPMap
#print axioms SpectralTheorem.borelPMap_bounded
#print axioms SpectralTheorem.borelPMap_id

-- PVMUnbounded, UnboundedSpectralPVM (M9: Theorem VIII.6)
#print axioms SpectralTheorem.ProjectionValuedMeasure.inner_integralPMap
#print axioms SpectralTheorem.ProjectionValuedMeasure.enorm_integralPMap_apply_sq
#print axioms SpectralTheorem.ProjectionValuedMeasure.dense_integralPMap_domain
#print axioms SpectralTheorem.ProjectionValuedMeasure.isSelfAdjoint_integralPMap
#print axioms SpectralTheorem.ProjectionValuedMeasure.adjoint_integralPMap
#print axioms SpectralTheorem.integral_pvm
#print axioms SpectralTheorem.integralPMap_pvm
#print axioms SpectralTheorem.ProjectionValuedMeasure.pvm_selfAdjointOp
#print axioms SpectralTheorem.selfAdjointOp_pvm
#print axioms SpectralTheorem.selfAdjointEquivPVM
#print axioms SpectralTheorem.existsUnique_selfAdjointOp_eq

-- Complexification, ComplexificationOperator (M10)
#print axioms SpectralTheorem.Complexification.norm_sq_eq
#print axioms SpectralTheorem.Complexification.inner_ofReal_ofReal
#print axioms SpectralTheorem.Complexification.norm_complexifyCLM
#print axioms SpectralTheorem.Complexification.adjoint_complexifyCLM
#print axioms SpectralTheorem.Complexification.complexifyHom
#print axioms SpectralTheorem.Complexification.complexifyCLM_descendCLM
#print axioms SpectralTheorem.Complexification.adjoint_complexifyPMap
#print axioms SpectralTheorem.Complexification.isSelfAdjoint_complexifyPMap_iff

-- RealCalculus, RealUnboundedBorel (M10: Theorem VIII.5 on a real Hilbert space)
#print axioms SpectralTheorem.conj_selfAdjointCalc
#print axioms SpectralTheorem.complexifyCLM_realCalc
#print axioms SpectralTheorem.norm_realCalc_le
#print axioms SpectralTheorem.tendsto_realCalc_apply_self
#print axioms SpectralTheorem.tendsto_realCalc_apply
#print axioms SpectralTheorem.realCalc_apply_of_eigen
#print axioms SpectralTheorem.isPositive_realCalc
#print axioms SpectralTheorem.IsRealSelfAdjointCalculus.eq_realCalc
#print axioms SpectralTheorem.existsUnique_isRealSelfAdjointCalculus
#print axioms SpectralTheorem.isStarProjection_realSpectralProjection
#print axioms SpectralTheorem.tendsto_sum_realSpectralProjection
#print axioms SpectralTheorem.Complexification.complexifyPMap_descendPMap
#print axioms SpectralTheorem.isSelfAdjoint_realBorelPMap
#print axioms SpectralTheorem.realBorelPMap_bounded
#print axioms SpectralTheorem.realBorelPMap_id
#print axioms SpectralTheorem.realSpectralProjection_Iio_eq_zero

-- RealCyclic, RealMultiplicationForm (M10: multiplication operator form over ℝ)
#print axioms SpectralTheorem.conj_cfcHom
#print axioms SpectralTheorem.conj_cyclicIsometry
#print axioms SpectralTheorem.CyclicDecomposition.exists_real
#print axioms SpectralTheorem.CyclicDecomposition.unitary_conj
#print axioms SpectralTheorem.exists_orthogonal_mulReal
#print axioms SpectralTheorem.exists_orthogonal_mulReal_finite
#print axioms SpectralTheorem.exists_orthogonal_mulReal_bounded
#print axioms SpectralTheorem.exists_orthogonal_mulReal_bounded_finite

-- RepSpectralMeasure, RepCyclic, RepDecomposition (representations of C(X))
#print axioms SpectralTheorem.integral_repMeasure
#print axioms SpectralTheorem.eq_repMeasure
#print axioms SpectralTheorem.repCyclicIsometry_toLp
#print axioms SpectralTheorem.repCyclicIsometry_mul
#print axioms SpectralTheorem.RepDecomposition.nonempty
#print axioms SpectralTheorem.RepDecomposition.unitary_apply
#print axioms SpectralTheorem.exists_unitary_mulL_rep
#print axioms SpectralTheorem.exists_unitary_mulL_rep_finite

-- RepPVM (p.v.m. of a representation of C(X))
#print axioms SpectralTheorem.toRep_repPVM
#print axioms SpectralTheorem.measure_repPVM
#print axioms SpectralTheorem.ProjectionValuedMeasure.ext_of_toRep
#print axioms SpectralTheorem.existsUnique_regular_pvm
#print axioms SpectralTheorem.existsUnique_pvm_toRep_eq
#print axioms SpectralTheorem.commute_repPVM
#print axioms SpectralTheorem.repPVMEquivRegular
#print axioms SpectralTheorem.repPVMEquiv

-- CommOperatorAlgebra (Gelfand representation, commuting families)
#print axioms SpectralTheorem.CommOperatorAlgebra.spectrum_coe
#print axioms SpectralTheorem.CommOperatorAlgebra.gelfandRep_gelfandTransform
#print axioms SpectralTheorem.CommOperatorAlgebra.norm_gelfandRep
#print axioms SpectralTheorem.CommOperatorAlgebra.range_gelfandRep
#print axioms SpectralTheorem.CommOperatorAlgebra.metrizableSpace_of_countable
#print axioms SpectralTheorem.CommOperatorAlgebra.isClosedEmbedding_jointEval
#print axioms SpectralTheorem.CommOperatorAlgebra.gelfandTransform_eq_comp_jointEval
#print axioms SpectralTheorem.CommOperatorAlgebra.image_eval_jointSpectrum
#print axioms SpectralTheorem.CommOperatorAlgebra.jointCalc_coord
#print axioms SpectralTheorem.CommOperatorAlgebra.gelfandRep_comp_normalEvalHomeomorph

-- CommutativeSpectral (commutative C*-algebras of operators; joint spectral theorem)
#print axioms SpectralTheorem.CommOperatorAlgebra.integral_commPVM
#print axioms SpectralTheorem.CommOperatorAlgebra.existsUnique_regular_commPVM
#print axioms SpectralTheorem.CommOperatorAlgebra.existsUnique_commPVM
#print axioms SpectralTheorem.CommOperatorAlgebra.commute_commPVM
#print axioms SpectralTheorem.CommOperatorAlgebra.exists_unitary_mulL_gelfandTransform
#print axioms SpectralTheorem.CommOperatorAlgebra.exists_unitary_mulL_gelfandTransform_finite
#print axioms SpectralTheorem.CommOperatorAlgebra.integral_jointPVM_coordBall
#print axioms SpectralTheorem.CommOperatorAlgebra.jointPVM_jointSpectrum
#print axioms SpectralTheorem.CommOperatorAlgebra.commute_jointPVM
#print axioms SpectralTheorem.CommOperatorAlgebra.existsUnique_jointPVM
#print axioms SpectralTheorem.CommOperatorAlgebra.exists_unitary_mulL_joint
#print axioms SpectralTheorem.CommOperatorAlgebra.exists_unitary_mulL_joint_real
#print axioms SpectralTheorem.CommOperatorAlgebra.integral_jointPVMReal_coordBallReal
#print axioms SpectralTheorem.CommOperatorAlgebra.existsUnique_jointPVMReal

-- VonNeumann (von Neumann's theorem on 1 + T†T; Reed–Simon II, Theorem X.25, p. 180)
#print axioms SpectralTheorem.vonNeumann_bijective
#print axioms SpectralTheorem.isSelfAdjoint_adjointComp
#print axioms SpectralTheorem.norm_vonNeumannInverse_le_one
#print axioms SpectralTheorem.range_vonNeumannInverse
#print axioms SpectralTheorem.norm_boundedOfCompose_le_one
#print axioms SpectralTheorem.hasCore_adjointCompDomain

-- NormalPMap, NormalSpectral, NormalSpectralProperties, NormalGeneral (unbounded normal operators)
#print axioms SpectralTheorem.IsNormalPMap.isClosed
#print axioms IsSelfAdjoint.isNormalPMap
#print axioms SpectralTheorem.ProjectionValuedMeasure.isNormalPMap_integralPMap
#print axioms SpectralTheorem.ProjectionValuedMeasure.integralPMap_star_integralPMap
#print axioms SpectralTheorem.ProjectionValuedMeasure.integralPMap_integralPMap_star
#print axioms SpectralTheorem.ProjectionValuedMeasure.isSelfAdjoint_integralPMap_iff
#print axioms SpectralTheorem.exists_pvm_integralPMap_eq
#print axioms SpectralTheorem.IsResolventAt.isNormalPMap
#print axioms SpectralTheorem.isSelfAdjoint_iff_apply_real_eq_one
#print axioms SpectralTheorem.adjoint_adjoint
#print axioms SpectralTheorem.IsNormalPMap.adjointComp_adjoint
#print axioms SpectralTheorem.IsNormalPMap.eq_of_le
#print axioms SpectralTheorem.IsNormalPMap.exists_pvm
