# Status: KatoRellich v0.1 (2026-09-21)

Nine modules; 1,701 lines including the root file and `checks/Axioms.lean`.  Every module
compiles without errors or warnings; the totalisation audit passes; the 26 declarations in
`checks/Axioms.lean` depend only on `propext`, `Classical.choice` and `Quot.sound`.  Compiled
module by module with `lean +leanprover/lean4:v4.34.0-rc2` against the mathlib build of
`FiniteVolumeYM2Phi42`; not yet built by `lake`, since no host project requires the library.

## Sources checked

Page images, 2026-09-21:

* Reed–Simon I (1972): definitions of symmetric and self-adjoint operators, p. 255; essential
  self-adjointness and cores, p. 256; Theorem VIII.3, pp. 256–257; quadratic forms, symmetric,
  semibounded, p. 276; the form of an operator (Example 2), closed forms, `‖·‖₊₁`, form cores,
  p. 277; Theorem VIII.15, p. 278, proof to p. 279.
* Reed–Simon II (1975): `A`-bounded operators and relative bound, (X.19a), p. 162; Theorem X.12,
  p. 162, proof p. 163.

## Process

`Basic`, `Criterion`, `BoundedPerturbation`, `Resolvent`, `Neumann`, `Theorem` and `Core` were
written by the lead.  `QuadraticForm` and `FormRepresentation` were written by a background agent
from a brief fixing the definitions and the proof plan, then reviewed against Reed–Simon I,
pp. 276–279; the review corrected two page references in their docstrings.

## Deviations from Reed–Simon

* Kato–Rellich over `ℝ` is proved only for `A` bounded below (see `README.md`).
* Theorem VIII.3 is proved only in the direction (c) ⟹ (a), which is the one the other results
  use, for an arbitrary pair of conjugate shifts `z`, `z̄`.
* Theorem VIII.15: self-adjointness is proved with the basic criterion (`Ran(T + M + 1) = H`)
  instead of Reed–Simon's Hellinger–Toeplitz and spectral-theorem step; uniqueness, which
  Reed–Simon leave as a problem, is proved; symmetry of the form is an explicit hypothesis.

## Next steps

1. **Lower bound in Theorem X.12**: `A ≥ M` implies `A + B ≥ M − max{b/(1−a), a|M| + b}`.  The
   estimates are available: `‖A x‖ ≤ max(1, |M|/(M+t)) ‖(A + t) x‖` follows from
   `K² ‖(A+t)x‖² − ‖Ax‖² = (K²−1)‖(A−M)x‖² + 2(K²s−M)⟪(A−M)x, x⟫ + (K²s²−M²)‖x‖²` with
   `s = M + t`.  They give `Ran(A + B + t) = H` for `−t < M − max{…}`.  To conclude `A + B ≥ −t`
   without the spectral theorem, use that `t ↦ ⟪(T + t)⁻¹ y, y⟫` has derivative
   `−‖(T + t)⁻¹ y‖² ≤ 0` (resolvent identity) and that `t ⟪(T + t)⁻¹ y, y⟫ → ‖y‖²` as `t → ∞`
   for `y ∈ D(T)`.  So `(T + t)⁻¹ ≥ 0` on the whole interval.  Estimated 300–400 lines.
2. Kato–Rellich on a real Hilbert space without a lower bound, through the complexification.
3. Add the library as a path dependency of a host project and confirm `lake build KatoRellich`.
