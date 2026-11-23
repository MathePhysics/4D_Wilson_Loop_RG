import KatoRellich

/-! Every main declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. -/

-- Basic
#print axioms KatoRellich.IsSymmetric.of_isSelfAdjoint
#print axioms KatoRellich.IsSymmetric.add

-- Criterion (Reed–Simon I, Theorem VIII.3)
#print axioms KatoRellich.isSelfAdjoint_of_range_addScalar
#print axioms KatoRellich.isSelfAdjoint_of_range_addScalar_ofReal

-- BoundedPerturbation
#print axioms KatoRellich.adjoint_addBounded
#print axioms KatoRellich.isSelfAdjoint_addBounded
#print axioms KatoRellich.isSelfAdjoint_add_toPMap
#print axioms KatoRellich.isSelfAdjoint_addBounded_neg

-- Resolvent
#print axioms KatoRellich.isClosed_range_of_isClosed
#print axioms KatoRellich.range_addScalar_eq_top
#print axioms KatoRellich.range_addScalar_ofReal_eq_top
#print axioms KatoRellich.range_addScalar_I_eq_top

-- Neumann
#print axioms KatoRellich.exists_add_eq_of_norm_le

-- Theorem (Reed–Simon II, Theorem X.12)
#print axioms KatoRellich.range_addScalar_add_eq_top_of_isRelBounded
#print axioms KatoRellich.isSelfAdjoint_add
#print axioms KatoRellich.isSelfAdjoint_add_complex
#print axioms KatoRellich.isSelfAdjoint_add_of_isBoundedBelow

-- Core
#print axioms KatoRellich.hasCore_add
#print axioms KatoRellich.isEssentiallySelfAdjoint_add
#print axioms KatoRellich.isEssentiallySelfAdjoint_add_of_isBoundedBelow

-- QuadraticForm, FormRepresentation (Reed–Simon I, Theorem VIII.15)
#print axioms KatoRellich.QuadForm.FormSpace.completeSpace
#print axioms KatoRellich.adjoint_le_adjoint
#print axioms KatoRellich.QuadForm.isSelfAdjoint_toOperator
#print axioms KatoRellich.QuadForm.isFormOf_toOperator
#print axioms KatoRellich.QuadForm.eq_toOperator_of_isSelfAdjoint
#print axioms KatoRellich.QuadForm.existsUnique_isSelfAdjoint_isFormOf
