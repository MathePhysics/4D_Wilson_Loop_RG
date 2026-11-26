import CoreLean.WilsonLoop.Statement

/-!
# Theorem 1.5 of [WL] ("Uniform Bound and Limit")

The theorem `CoreLean.WilsonLoop.boundAndLimit`: for a compact connected simple gauge group,
the conclusions of [WL] Theorem 1.5 and of [WL] `prop:nonvanishing` hold, in the form
`CoreLean.WilsonLoop.BoundAndLimit`.

The assumptions are those of [WL] l.83, "a compact connected simple Lie group in a fixed
unitary realisation `G ⊂ U(N)`": `G` is a `CoreLean.GaugeGroup`, a subgroup of unitary matrices;
it is compact (`CompactSpace G.carrier`), connected, and simple (`CoreLean.GaugeGroup.IsSimple`).

The theorem is stated and not proved.
-/

namespace CoreLean

namespace WilsonLoop

variable {N : ℕ}

/-- **Theorem 1.5 of [WL]** (Uniform Bound and Limit), with the lower bound of
`prop:nonvanishing`, for a compact connected simple gauge group. -/
theorem boundAndLimit (G : GaugeGroup N) [CompactSpace G.carrier]
    (hconn : IsConnected (G.carrier : Set (Matrix (Fin N) (Fin N) ℂ)ˣ)) (hsimple : G.IsSimple) :
    BoundAndLimit G := by
  sorry

end WilsonLoop

end CoreLean
