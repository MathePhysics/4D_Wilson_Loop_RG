import BlockPoincare

/-! Every main declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. -/

-- Defs
#print axioms BlockPoincare.l2sq
#print axioms BlockPoincare.mean
#print axioms BlockPoincare.gagliardoSq
#print axioms BlockPoincare.hsNormSq
#print axioms BlockPoincare.unitBall
#print axioms BlockPoincare.hNegNorm
#print axioms BlockPoincare.l2sq_toReal
#print axioms BlockPoincare.gagliardoSq_mono_set
#print axioms BlockPoincare.gagliardoSq_add_const
#print axioms BlockPoincare.neg_mem_unitBall
#print axioms BlockPoincare.le_hNegNorm
#print axioms BlockPoincare.hNegNorm_le
#print axioms BlockPoincare.hNegNorm_zero

-- Cube
#print axioms BlockPoincare.integral_sub_mean_sq_le
#print axioms BlockPoincare.mul_l2sq_sub_mean_le
#print axioms BlockPoincare.lintegral_sq_diff_le
#print axioms BlockPoincare.mul_l2sq_sub_mean_le_diam
#print axioms BlockPoincare.l2sq_sub_mean_le_diam

-- Blocks
#print axioms BlockPoincare.BlockPartition
#print axioms BlockPoincare.BlockPartition.sum_setLIntegral
#print axioms BlockPoincare.BlockPartition.sum_l2sq
#print axioms BlockPoincare.BlockPartition.sum_gagliardoSq_le
#print axioms BlockPoincare.BlockPartition.sum_setIntegral

-- Estimate
#print axioms BlockPoincare.integral_mul_le_sqrt_mul_sqrt
#print axioms BlockPoincare.integral_sub_bmean_sq_le
#print axioms BlockPoincare.pairing_le
#print axioms BlockPoincare.memLp_two_of_l2sq_ne_top
#print axioms BlockPoincare.memLp_two_of_mem_unitBall
#print axioms BlockPoincare.hNegNorm_le_of_blockIntegral_zero

-- Nontrivial
#print axioms BlockPoincare.l2sq_const_mul
#print axioms BlockPoincare.gagliardoSq_const_mul
#print axioms BlockPoincare.hsNormSq_const_mul
#print axioms BlockPoincare.hNegNorm_pos

-- Scales
#print axioms BlockPoincare.sqrt_cube_const
#print axioms BlockPoincare.hNegNorm_le_cube
#print axioms BlockPoincare.scale
#print axioms BlockPoincare.summable_scale_rpow
#print axioms BlockPoincare.hNegNorm_le_scale

-- Centred
#print axioms BlockPoincare.BlockPartition.measure_univ_eq
#print axioms BlockPoincare.BlockPartition.isFiniteMeasure
#print axioms BlockPoincare.BlockPartition.centre
#print axioms BlockPoincare.BlockPartition.centre_apply
#print axioms BlockPoincare.BlockPartition.setIntegral_centre
#print axioms BlockPoincare.BlockPartition.centre_eq_self_of_setIntegral_eq_zero
#print axioms BlockPoincare.BlockPartition.centre_idem
#print axioms BlockPoincare.BlockPartition.memLp_centre
#print axioms BlockPoincare.BlockPartition.hNegNorm_centre_le

-- Torus, Product
#print axioms BlockPoincare.Torus.dist_coe_le
#print axioms BlockPoincare.Torus.coord
#print axioms BlockPoincare.Torus.arc
#print axioms BlockPoincare.Torus.volume_arc
#print axioms BlockPoincare.Torus.arc_disjoint
#print axioms BlockPoincare.Torus.iUnion_arc
#print axioms BlockPoincare.Torus.dist_le_of_mem_arc
#print axioms BlockPoincare.Torus.arcs
#print axioms BlockPoincare.Torus.hNegNorm_le_arcs
#print axioms BlockPoincare.BlockPartition.prod
#print axioms BlockPoincare.Torus.squares
#print axioms BlockPoincare.Torus.sqrt_square_const
#print axioms BlockPoincare.Torus.hNegNorm_le_squares
#print axioms BlockPoincare.Torus.hNegNorm_le_scale_pow
#print axioms BlockPoincare.Torus.summable_torus_scale
#print axioms BlockPoincare.Torus.hNegNorm_centre_le_squares

-- Witness
#print axioms BlockPoincare.TwoPoint.instMetricSpace
#print axioms BlockPoincare.TwoPoint.count_univ_eq
#print axioms BlockPoincare.TwoPoint.blocks
#print axioms BlockPoincare.TwoPoint.witness
#print axioms BlockPoincare.TwoPoint.integral_witness
#print axioms BlockPoincare.TwoPoint.integral_witness_sq
#print axioms BlockPoincare.TwoPoint.gagliardoSq_witness
#print axioms BlockPoincare.TwoPoint.hsNormSq_witness
#print axioms BlockPoincare.TwoPoint.hNegNorm_witness_pos
#print axioms BlockPoincare.TwoPoint.hNegNorm_witness_le
#print axioms BlockPoincare.TwoPoint.hNegNorm_witness_le_one
#print axioms BlockPoincare.TwoPoint.witness_nontrivial
