import BakerCampbellHausdorff

/-! Every main declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. -/

-- ExpBounds
#print axioms BakerCampbellHausdorff.exp_add_of_commute'
#print axioms BakerCampbellHausdorff.norm_exp_sub_one_sub_le
#print axioms BakerCampbellHausdorff.norm_exp_mul_exp_sub_one_le
#print axioms BakerCampbellHausdorff.eq_zero_of_exp_eq_one

-- LogSeries
#print axioms BakerCampbellHausdorff.one_le_radius_logSeries
#print axioms BakerCampbellHausdorff.hasFPowerSeriesOnBall_log1p
#print axioms BakerCampbellHausdorff.analyticOnNhd_log1p
#print axioms BakerCampbellHausdorff.norm_log1p_le
#print axioms Commute.log1p_right

-- ExpLog, LogExp
#print axioms BakerCampbellHausdorff.exp_log1p
#print axioms BakerCampbellHausdorff.log1p_exp_sub_one
#print axioms BakerCampbellHausdorff.exp_injOn
#print axioms BakerCampbellHausdorff.eq_log1p_of_exp_eq

-- AnalyticLog
#print axioms FormalMultilinearSeries.exists_geometricBound
#print axioms BakerCampbellHausdorff.GeometricBound.radius_pos
#print axioms BakerCampbellHausdorff.GeometricBound.compContinuousLinearMap
#print axioms BakerCampbellHausdorff.GeometricBound.compFormalMultilinearSeries
#print axioms HasFPowerSeriesAt.log1p_sub_one
#print axioms HasFPowerSeriesAt.exists_geometricBound_log
#print axioms AnalyticOnNhd.log1p_sub_one
#print axioms ContinuousAt.eventually_exp_log1p_sub_one

-- ExpMulExpSeries
#print axioms BakerCampbellHausdorff.expMulExpSeries_radius
#print axioms BakerCampbellHausdorff.hasFPowerSeriesOnBall_exp_mul_exp
#print axioms BakerCampbellHausdorff.expMulExpSeries_two_apply_diag

-- Theorem
#print axioms BakerCampbellHausdorff.exp_bch
#print axioms BakerCampbellHausdorff.eq_bch_of_exp_eq
#print axioms BakerCampbellHausdorff.hasFPowerSeriesAt_bch
#print axioms BakerCampbellHausdorff.exists_geometricBound_bchSeries
#print axioms BakerCampbellHausdorff.analyticOnNhd_bch
#print axioms BakerCampbellHausdorff.hasFDerivAt_bch
#print axioms BakerCampbellHausdorff.bchSeries_two_apply_diag
#print axioms BakerCampbellHausdorff.bch_sub_isBigO
#print axioms BakerCampbellHausdorff.norm_bch_le
#print axioms BakerCampbellHausdorff.bch_eq_add_of_commute

-- GroupLaw
#print axioms BakerCampbellHausdorff.norm_bch_le_mul
#print axioms BakerCampbellHausdorff.bch_neg_neg
#print axioms BakerCampbellHausdorff.bch_assoc

-- Product
#print axioms BakerCampbellHausdorff.exp_bchProd
#print axioms BakerCampbellHausdorff.eq_bchProd_of_exp_eq
#print axioms BakerCampbellHausdorff.analyticOnNhd_bchProd
#print axioms BakerCampbellHausdorff.exists_hasFPowerSeriesAt_bchProd
#print axioms BakerCampbellHausdorff.exists_hasFPowerSeriesAt_bchProd_comp

-- Operators, Dexp
#print axioms BakerCampbellHausdorff.exp_ad
#print axioms BakerCampbellHausdorff.norm_expSubOneDiv_sub_one_le
#print axioms BakerCampbellHausdorff.sum_pow_mul_pow_mul_choose
#print axioms BakerCampbellHausdorff.hasDerivAt_exp_add_smul
#print axioms BakerCampbellHausdorff.hasFDerivAt_exp

-- Lie
#print axioms BakerCampbellHausdorff.ad_log1p_mem_preserving
#print axioms BakerCampbellHausdorff.log1p_mem_of_dexp
#print axioms BakerCampbellHausdorff.mem_of_forall_dual
#print axioms BakerCampbellHausdorff.coeff_mem_of_hasFPowerSeriesAt
#print axioms BakerCampbellHausdorff.bch_mem
#print axioms BakerCampbellHausdorff.bchProd_mem
#print axioms BakerCampbellHausdorff.bchSeries_apply_diag_mem
#print axioms BakerCampbellHausdorff.bch_mem_of_isScalarTower
#print axioms BakerCampbellHausdorff.bchProd_mem_of_isScalarTower

-- MulSeries, ExpProdSeries
#print axioms BakerCampbellHausdorff.norm_mulSeries_le
#print axioms HasFPowerSeriesOnBall.mulSeries
#print axioms BakerCampbellHausdorff.hasFPowerSeriesOnBall_expProd
#print axioms BakerCampbellHausdorff.norm_expProdSeries_le
#print axioms BakerCampbellHausdorff.expProdSeries_one_apply

-- Explicit
#print axioms BakerCampbellHausdorff.norm_logSeries_comp_le
#print axioms BakerCampbellHausdorff.geometricBound_bchSeries
#print axioms BakerCampbellHausdorff.hasFPowerSeriesOnBall_bch
#print axioms BakerCampbellHausdorff.norm_bch_sub_partialSum_le
#print axioms BakerCampbellHausdorff.geometricBound_bchProdSeries
#print axioms BakerCampbellHausdorff.hasFPowerSeriesOnBall_bchProd
#print axioms BakerCampbellHausdorff.norm_bchProd_sub_partialSum_le
#print axioms BakerCampbellHausdorff.bchProdSeries_one_apply
#print axioms BakerCampbellHausdorff.norm_bchProdSeries_comp_le
#print axioms BakerCampbellHausdorff.geometricBound_bchProdSeries_comp
#print axioms BakerCampbellHausdorff.bchProdSeries_comp_one_apply
#print axioms BakerCampbellHausdorff.hasFDerivAt_bchProd_comp
#print axioms BakerCampbellHausdorff.bchProd_comp_sub_sum_isBigO
#print axioms BakerCampbellHausdorff.norm_bchProd_comp_sub_partialSum_le

-- ExpTaylor
#print axioms BakerCampbellHausdorff.exp_eq_sum_add_expRem
#print axioms BakerCampbellHausdorff.norm_expRem_le_one
#print axioms BakerCampbellHausdorff.smul_integral_pow_smul_exp
