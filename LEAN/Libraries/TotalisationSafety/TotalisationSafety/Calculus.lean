import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Derivatives with witnesses

`fderiv` is total and uses a zero fallback away from differentiability.  The structure below stores
an actual derivative together with `HasFDerivAt`, so downstream code need never infer mathematical
differentiability from the value returned by `fderiv`.
-/

namespace TotalisationSafety

/-- A Fréchet derivative at a point, bundled with the proposition that it is the derivative. -/
structure FrechetDerivativeAt
    (𝕜 : Type*) (E : Type*) (F : Type*)
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (x : E) where
  derivative : E →L[𝕜] F
  hasFDerivAt : HasFDerivAt f derivative x

end TotalisationSafety
