import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Functional-analysis inventory for the Friedrichs extension project

This file intentionally contains only API probes.  Its purpose is to pin the mathlib
infrastructure on which the project will build, and to fail loudly if one of these names changes.
-/

#check InnerProductSpace.Core
#check InnerProductSpace.Core.toNormedAddCommGroup
#check InnerProductSpace.ofCore
#check UniformSpace.Completion
#check InnerProductSpace.toDual
#check IsCoercive
#check IsCoercive.continuousLinearEquivOfBilin
#check Submodule.orthogonalProjectionOnto

#check LinearPMap.IsClosed
#check LinearPMap.IsClosable
#check LinearPMap.closure
#check LinearPMap.HasCore
#check LinearPMap.IsFormalAdjoint
#check LinearPMap.adjoint
#check IsSelfAdjoint
#check IsSelfAdjoint.dense_domain
#check IsSelfAdjoint.isClosed

#check ContinuousLinearMap.IsPositive
#check ContinuousLinearMap.isOpenMap
#check ContinuousLinearMap.ofIsClosedGraph
#check banach_steinhaus
