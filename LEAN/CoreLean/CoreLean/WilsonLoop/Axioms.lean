import CoreLean.WilsonLoop.MainTheorem
import CoreLean.WilsonLoop.NegativeControl
import CoreLean.WilsonLoop.Sanity.Gauge
import CoreLean.WilsonLoop.Sanity.Limit
import CoreLean.WilsonLoop.Sanity.Measure
import CoreLean.WilsonLoop.Sanity.Representation
import CoreLean.WilsonLoop.Sanity.Square

/-!
# Axioms used

The RG construction and the results derived from it depend on `sorryAx`. The statement
checks are proved from the three standard axioms of Lean and Mathlib.
Each `#guard_msgs` below fails the build if the list of axioms of
the declaration changes.
-/

/--
info: 'CoreLean.WilsonLoop.boundAndLimit' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.boundAndLimit

/--
info: 'CoreLean.WilsonLoop.nonvanishing' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.nonvanishing

/--
info: 'CoreLean.WilsonLoop.existentialBoundAndLimit' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.existentialBoundAndLimit

/-- info: 'CoreLean.WilsonLoop.boundOnly_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.boundOnly_trivial

/--
info: 'CoreLean.WilsonLoop.ExistentialBoundAndLimit.boundOnly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.ExistentialBoundAndLimit.boundOnly

/--
info: 'CoreLean.WilsonLoop.Ensemble.observable_gauge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.Ensemble.observable_gauge

/--
info: 'CoreLean.WilsonLoop.Loop.character_hol_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.Loop.character_hol_rotate

/--
info: 'CoreLean.WilsonLoop.MainBound.exists_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.MainBound.exists_limit

/--
info: 'CoreLean.WilsonLoop.isProbabilityMeasure_haarField' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.isProbabilityMeasure_haarField

/--
info: 'CoreLean.WilsonLoop.Irrep.IsDifferential.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.Irrep.IsDifferential.unique

/--
info: 'CoreLean.WilsonLoop.unitSquare_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.unitSquare_separation

/--
info: 'CoreLean.WilsonLoop.unitSquare_isolationRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.unitSquare_isolationRatio

/--
info: 'CoreLean.WilsonLoop.unitSquare_chordArcLE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CoreLean.WilsonLoop.unitSquare_chordArcLE
