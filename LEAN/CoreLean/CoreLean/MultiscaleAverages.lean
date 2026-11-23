/-
The concrete layer, step C3 (`CONCRETE_LAYER.md`): the averages of a sequence of BALABAN_CORE.tex (`615c66b253fe`,
`def:average`, `def:relative-average-order`, `def:operators`(i)), on the lattices in their own units.

Model. `L = 2h + 1`. The lattice `T^{(j)}` in the units of the scale `j` is `Site (nn h m k j)` with
`nn h m k j = 2L^{m + (k - j)} = ℓ_𝕋/a_j`; its points are the points `L^j x` of the fine lattice. A site `y` of
`T^{(j+1)}` is the point `Ly` of `T^{(j)}` (`up`).

* `Mcfg`: the average `M` of `def:average` from `T^{(j)}` to `T^{(j+1)}`, `M(V)_κ(y) = avgG V (Ly) κ` (the average of the
  family `𝐆` at the coarse bond `(y, y + a_{j+1}e_κ)`), with the domain of the group mean `inN` and the logarithm
  `log` of `def:group-mean` as parameters; `Mpow U j = M^j(U)`.
* `Qstep V`: the linear part `Q(V)` of the relative average (`eq:linear-part`, `RelativeAverage.Qlin`) at every coarse
  bond, a linear map from the `1`-forms of `T^{(j)}` to those of `T^{(j+1)}`.
* `Qcomp U j = Q_j(U) = Q(U^{(j-1)}) ⋯ Q(U^{(0)})` with `U^{(i)} = M^i(U)` (`eq:composite-linear-part`), `Q_0 = I`.
-/
import CoreLean.RelativeAverageLinear
import CoreLean.AverageCanonical

noncomputable section

namespace CoreLean
namespace MultiscaleAverages

open RelativeAverage

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `ℓ_𝕋/a_j = 2L^{m + (k - j)}`, `L = 2h + 1`. -/
def nn (h m k j : ℕ) : ℕ := 2 * (2 * h + 1) ^ (m + (k - j))

instance (h m k j : ℕ) : NeZero (nn h m k j) := ⟨by unfold nn; positivity⟩

/-- `nn j = L · nn (j + 1)` for `j < k`. -/
lemma nn_succ (h m k j : ℕ) (hj : j < k) : nn h m k j = (2 * h + 1) * nn h m k (j + 1) := by
  unfold nn
  have : m + (k - j) = (m + (k - (j + 1))) + 1 := by omega
  rw [this, pow_succ]; ring

/-- The site `Ly` of `T^{(j)}` of a site `y` of `T^{(j+1)}`. -/
def up (h m k j : ℕ) (y : Site (nn h m k (j + 1))) : Site (nn h m k j) :=
  fun ν => (((2 * h + 1) * (y ν).val : ℕ) : ZMod (nn h m k j))

/-- `up` is injective for `j < k`: `Ly = Ly'` in `ℤ/(L·nn(j+1))` forces `y = y'`. -/
lemma up_injective (h m k j : ℕ) (hj : j < k) : Function.Injective (up h m k j) := by
  intro y y' hyy
  funext ν
  have h1 := congrFun hyy ν
  simp only [up] at h1
  rw [ZMod.natCast_eq_natCast_iff', nn_succ h m k j hj] at h1
  have hL : 0 < 2 * h + 1 := by omega
  simp only [Nat.mul_mod_mul_left] at h1
  have h2 := Nat.eq_of_mul_eq_mul_left hL h1
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
  exact ZMod.val_injective _ h2

variable (h m k : ℕ)

/-- **The average** `M` from `T^{(j)}` to `T^{(j+1)}`: `M(V)_κ(y) = avgG V (Ly) κ`. -/
def Mcfg (inN : GLN → Prop) (log : GLN → Mat) (j : ℕ) (V : Config N (nn h m k j)) : Config N (nn h m k (j + 1)) :=
  fun κ y => AverageHolo.avgG inN log V (up h m k j y) κ h (2 * h + 1)

/-- `M^j(U)`, the averaged configuration on `T^{(j)}`. -/
def Mpow (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) : ∀ j, Config N (nn h m k j)
  | 0 => U
  | j + 1 => Mcfg h m k inN log j (Mpow inN log U j)

/-- **The linear part of the relative average** at every coarse bond, `(Q(V)B)_κ(y) = Q(V)B` at `(Ly, κ)`. -/
def Qstep (j : ℕ) (V : Config N (nn h m k j)) : Form1 N (nn h m k j) →ₗ[ℂ] Form1 N (nn h m k (j + 1)) :=
  LinearMap.pi fun κ => LinearMap.pi fun y => (Qlin V (up h m k j y) κ h).toLinearMap

@[simp] lemma Qstep_apply (j : ℕ) (V : Config N (nn h m k j)) (B : Form1 N (nn h m k j)) (κ : Fin 4)
    (y : Site (nn h m k (j + 1))) : Qstep h m k j V B κ y = Qlin V (up h m k j y) κ h B := rfl

/-- **`Q_j(U) = Q(U^{(j-1)}) ⋯ Q(U^{(0)})`** (`eq:composite-linear-part`), `Q_0 = I`. -/
def Qcomp (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) :
    ∀ j, Form1 N (nn h m k 0) →ₗ[ℂ] Form1 N (nn h m k j)
  | 0 => LinearMap.id
  | j + 1 => Qstep h m k j (Mpow h m k inN log U j) ∘ₗ Qcomp inN log U j

@[simp] lemma Qcomp_zero (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) :
    Qcomp h m k inN log U 0 = LinearMap.id := rfl

lemma Qcomp_succ (inN : GLN → Prop) (log : GLN → Mat) (U : Config N (nn h m k 0)) (j : ℕ) :
    Qcomp h m k inN log U (j + 1) = Qstep h m k j (Mpow h m k inN log U j) ∘ₗ Qcomp h m k inN log U j := rfl

/-- **The canonical average**: with the series `Log` (`inN = True`, `log = LogM`, the extension of `lem:average`(vi)
to complex configurations), `M` is the average `avgM` of `def:average`, on which the relative average, its linear
part, and `prop:relative-average-order` are stated. -/
theorem Mcfg_LogM (j : ℕ) (V : Config N (nn h m k j)) (κ : Fin 4) (y : Site (nn h m k (j + 1))) :
    Mcfg h m k (fun _ => True) (fun W => LogM (W : Mat)) j V κ y = avgM V (up h m k j y) κ h := by
  unfold Mcfg avgM
  rw [AverageHolo.avgLogU_eq_avgLogZ, AverageHolo.avgLogZ_eq_avgZ]
  rfl

end MultiscaleAverages
end CoreLean

end
