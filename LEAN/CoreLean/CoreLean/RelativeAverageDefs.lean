/-
The objects of `def:group-mean`(ii) and `def:relative-average` of BALABAN_CORE.tex (`d8bdc4ac1777`) on the lattice
of `Lattice.lean`, for `prop:relative-average`.

The fine lattice `T^{(j-1)}` is the torus `Site n` with spacing one (the spacing enters only through `aA`, which is
the `1`-form `B` here, `prop:relative-average`(viii)); the block of `y` is `B(y) = {y + n | |n|_∞ ≤ h}`, `L = 2h + 1`,
with the points `Pts h` and the offsets `offP h`, and the paths of `𝐆(y, x)` are the paths `stair` of the orderings
`Ords` (`def:block-paths`, `BlockPaths.lean`).

* `holG V y h x Γ`: `𝐔(Γ)` for `Γ ∈ 𝐆(y, x)`.
* `trans V y h x`: the transport `𝐔(y, x) = 𝗆({𝐔(Γ)}_{Γ ∈ 𝐆(y, x)})`, the mean of `def:group-mean`(i) with the
  first element `𝐖₁ = 𝐔(Γ₀)` of a fixed enumeration of `𝐆(y, x)` and the exponents `Yᵢ = (1/i) Log(𝐖ᵢ𝐖₁⁻¹)`.
* `siteFactor V B y h`: `v_𝐔(A)(y) = exp(L⁻⁴ Σ_{x ∈ B(y)} Log(𝐔_A(y, x)𝐔(y, x)⁻¹))`, `𝐔_A = e^{iB}𝐔`
  (`eq:site-factor`).
* `relAvg V B y μ h`: `𝓜_𝐔(A)(c) = v(c₋)⁻¹ M(𝐔_A)(c) v(c₊) M(𝐔)(c)⁻¹` for `c = (y, y + Le_μ)`, with the average
  `avgLogU` of `lem:average`(vi) (`eq:relative-average`).
* `blockAvg V λ y h`: `(Q'(𝐔)λ)(y) = L⁻⁴ Σ_{x ∈ B(y)} Ad_{𝐔(y, x)} λ(x)` (`eq:block-average`).
-/
import CoreLean.MeanTransports
import CoreLean.AverageHolo
import CoreLean.BlockPaths
import CoreLean.GroupMeanHolo

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The number of the paths of `𝐆(y, x)`. -/
abbrev nG (h : ℕ) (x : Pts h) : ℕ := Fintype.card (Ords (offP h x))

/-- An enumeration of the paths of `𝐆(y, x)`. -/
def enumG (h : ℕ) (x : Pts h) : Fin (nG h x) ≃ Ords (offP h x) := (Fintype.equivFin _).symm

/-- The first path of the enumeration. -/
def firstG (h : ℕ) (x : Pts h) : Ords (offP h x) := enumG h x ⟨0, card_ords_pos _⟩

/-- `𝐔(Γ)` for `Γ ∈ 𝐆(y, x)`. -/
def holG (V : Config N n) (y : Site n) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) : GLN :=
  V.hol (stair y (offP h x) (ordG h x Γ) 0)

/-- The exponents `Yᵢ = (1/i) Log(𝐔(Γᵢ)𝐔(Γ₀)⁻¹)` of the paths relative to the first. -/
def expsG (V : Config N n) (y : Site n) (h : ℕ) (x : Pts h) : Fin (nG h x) → Mat := fun i =>
  (1 / Complex.I : ℂ) • LogM ((holG V y h x (enumG h x i) * (holG V y h x (firstG h x))⁻¹ : GLN) : Mat)

/-- `def:group-mean`(ii): the transport `𝐔(y, x)`. -/
def trans (V : Config N n) (y : Site n) (h : ℕ) (x : Pts h) : GLN :=
  mean (expsG V y h x) (holG V y h x (firstG h x))

/-- `eq:site-factor`: the site factor `v_𝐔(A)(y)`, `B = aA`. -/
def siteFactor (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (h : ℕ) : GLN :=
  expU ((((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ •
    ∑ x : Pts h, LogM ((trans (moveC V B) y h x * (trans V y h x)⁻¹ : GLN) : Mat))

/-- The average `M(𝐔)(c)` of the bond `c = (y, y + Le_μ)` for the family `𝐆`, with the series `Log`. -/
def avgM (V : Config N n) (y : Site n) (μ : Fin 4) (h : ℕ) : GLN :=
  avgLogU (ι := Pts h) (P := fun x => Ords (offP h x)) V y μ (2 * h + 1) (offP h) (ordG h)

/-- The upper end `c₊ = y + Le_μ` of the bond. -/
def cPlus (y : Site n) (μ : Fin 4) (h : ℕ) : Site n := ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))

/-- `eq:relative-average`: `𝓜_𝐔(A)(c) = v(c₋)⁻¹ M(𝐔_A)(c) v(c₊) M(𝐔)(c)⁻¹`. -/
def relAvg (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) (h : ℕ) : GLN :=
  (siteFactor V B y h)⁻¹ * avgM (moveC V B) y μ h * siteFactor V B (cPlus y μ h) h * (avgM V y μ h)⁻¹

/-- `eq:average-of-product`: `M(e^{iB}𝐔)(c) = v(c₋) 𝓜_𝐔(A)(c) M(𝐔)(c) v(c₊)⁻¹`. -/
theorem average_of_product (V : Config N n) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4) (h : ℕ) :
    avgM (moveC V B) y μ h =
      siteFactor V B y h * relAvg V B y μ h * avgM V y μ h * (siteFactor V B (cPlus y μ h) h)⁻¹ := by
  simp only [relAvg]; group

/-- `eq:block-average`: `(Q'(𝐔)λ)(y) = L⁻⁴ Σ_{x ∈ B(y)} Ad_{𝐔(y, x)} λ(x)`. -/
def blockAvg (V : Config N n) (lam : Site n → Mat) (y : Site n) (h : ℕ) : Mat :=
  (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹ • ∑ x : Pts h, Ad (trans V y h x) (lam (ofs y (offP h x)))

end RelativeAverage
end CoreLean

end
