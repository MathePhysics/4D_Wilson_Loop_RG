import PeterWeyl

/-! Every main declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. -/

-- Basic
#print axioms PeterWeyl.haarProbability
#print axioms PeterWeyl.eq_haarProbability
#print axioms PeterWeyl.rightTranslate
#print axioms PeterWeyl.rightTranslateL2
#print axioms PeterWeyl.isContinuousUnitary_rightRegular
#print axioms PeterWeyl.IsContinuousUnitary.coeff_mem_matrixCoefficients
#print axioms PeterWeyl.star_mem_matrixCoefficients
#print axioms PeterWeyl.rightTranslate_mem_matrixCoefficients
#print axioms PeterWeyl.convolutionFun_eq_inner

-- ConvolutionOperator
#print axioms PeterWeyl.convolutionC
#print axioms PeterWeyl.norm_convolutionC_le
#print axioms PeterWeyl.equicontinuous_convolutionC
#print axioms PeterWeyl.isCompactOperator_convolutionC
#print axioms PeterWeyl.isCompactOperator_convolutionOperator
#print axioms PeterWeyl.convolutionOperator_rightTranslateL2
#print axioms PeterWeyl.adjoint_convolutionOperator
#print axioms PeterWeyl.isSelfAdjoint_convolutionOperator

-- InvariantSubspaces
#print axioms PeterWeyl.eigenSubrep
#print axioms PeterWeyl.finiteDimensional_eigenSubrep
#print axioms PeterWeyl.isContinuousUnitary_eigenSubrep
#print axioms PeterWeyl.coeff_eigenSubrep_mem_matrixCoefficients
#print axioms PeterWeyl.eigenspace_le_map_matrixCoefficients
#print axioms PeterWeyl.iSup_eigenspace_le_comap_factor

-- ApproximateIdentity
#print axioms PeterWeyl.exists_symmetric_bump
#print axioms PeterWeyl.exists_approxKernel
#print axioms PeterWeyl.exists_nhds_one_convolutionFun_approx
#print axioms PeterWeyl.exists_convolutionFun_approx
