/-
The concrete layer, first instantiation (`CONCRETE_LAYER.md`, C1 → C7): `thm:critical`(ii) and (iii) of
BALABAN_CORE.tex (`615c66b253fe`) with the concrete pairings. The `1`-forms are `Form1 N n` with `⟨·,·⟩` of
`eq:pairing` at the spacing `a > 0` (`ConcretePairing.pairForm1`), the functions on the bonds of the layers are
`ι → Mat` for a finite index set `ι` with the pairing `(μ, ν)_w = Σ_c a_c⁴tr μ(c)ν(c)`, `a_c > 0`
(`ConcretePairing.wpair`), and `Q^*` is the transpose of `Q` (`def:operators`(iii)). The hypotheses on the pairings in
`CriticalTheorem` (nondegeneracy, symmetry, `⟨Q^*μ, A⟩ = (μ, QA)`) are then proved
(`critical_ii_concrete`, `Gtilde_J_concrete`); the remaining hypotheses are those on the operators and the cited
analytic results.
-/
import CoreLean.CriticalTheorem
import CoreLean.ConcretePairing

open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace CriticalConcrete

open ConcretePairing CriticalTheorem

variable {N n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The pairing of the functions on the bonds of the layers, `(μ, ν)_w = Σ_c a_c⁴tr μ(c)ν(c)`. -/
abbrev pairF (ac : ι → ℝ) : BilinForm ℂ (ι → Mat) := wpair fun c => ((ac c ^ 4 : ℝ) : ℂ)

/-- `Q^*`, the transpose of `Q` with respect to `⟨·,·⟩` and `(·,·)_w`. -/
abbrev Qstar {a : ℝ} (ha : 0 < a) (ac : ι → ℝ) (Q : Form1 N n →ₗ[ℂ] (ι → Mat)) : (ι → Mat) →ₗ[ℂ] Form1 N n :=
  transpose (pairForm1 (a : ℂ)) (pairF ac) (pairForm1_nondegenerate ha) Q

/-- **`thm:critical`(ii) with the concrete pairings**: `A = 𝓗(𝖷(A))`, the hypotheses on the pairings proved. -/
theorem critical_ii_concrete {a : ℝ} (ha : 0 < a) (ac : ι → ℝ) (hac : ∀ c, 0 < ac c)
    (Q : Form1 N n →ₗ[ℂ] (ι → Mat)) (Δ Δ₂ DRD Gc G : Form1 N n →ₗ[ℂ] Form1 N n)
    (aa Minv M0inv : (ι → Mat) →ₗ[ℂ] (ι → Mat))
    (hGc : ∀ x, Gc ((Delta_a Q (Qstar ha ac Q) Δ DRD aa - Δ₂) x) = x)
    (hGc' : ∀ x, (Delta_a Q (Qstar ha ac Q) Δ DRD aa - Δ₂) (Gc x) = x)
    (hM : ∀ ν, Minv (Q (Gc (Qstar ha ac Q ν))) = ν) (hG : ∀ x, Delta_a Q (Qstar ha ac Q) Δ DRD aa (G x) = x)
    (hM0 : ∀ y, Q (G (Qstar ha ac Q (M0inv y))) = y) (Nf : Form1 N n → Form1 N n) (J : Form1 N n)
    (T : Form1 N n → Form1 N n) (X : Form1 N n → (ι → Mat)) (A0fix : Form1 N n → Form1 N n)
    (ball : Form1 N n → Set (Form1 N n))
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, Phi0 Q (Qstar ha ac Q) Δ₂ Gc Minv Nf J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄)
    (A A' : Form1 N n) (hT : T A' = A) (hD : DRD A' = 0) (hX : Q A' = X A)
    (hcrit : ∀ δ, Q δ = 0 → pairForm1 (a : ℂ) (J + (Δ - Δ₂) A' + Nf A') δ = 0)
    (hball : A' - H0 (Qstar ha ac Q) G M0inv (X A) ∈ ball (H0 (Qstar ha ac Q) G M0inv (X A))) :
    A = T (A0fix (H0 (Qstar ha ac Q) G M0inv (X A)) + H0 (Qstar ha ac Q) G M0inv (X A)) :=
  critical_ii Q (Qstar ha ac Q) Δ Δ₂ DRD Gc G aa Minv M0inv (pairForm1 (a : ℂ)) (pairF ac)
    (pairForm1_nondegenerate ha) (wpair_nondegenerate _ fun c => by have := hac c; positivity)
    (transpose_spec _ _ _ Q) hGc hGc' hM hG hM0 Nf J T X A0fix ball huniq A A' hT hD hX hcrit hball

/-- **`G̃J = 0` with the concrete pairings**, at a critical `U₀`: the symmetry and nondegeneracy hypotheses proved. -/
theorem Gtilde_J_concrete {a : ℝ} (ha : 0 < a) (ac : ι → ℝ) (Q : Form1 N n →ₗ[ℂ] (ι → Mat))
    (Gc : Form1 N n →ₗ[ℂ] Form1 N n) (Minv : (ι → Mat) →ₗ[ℂ] (ι → Mat))
    (hGcs : ∀ x y, pairForm1 (a : ℂ) (Gc x) y = pairForm1 (a : ℂ) x (Gc y))
    (hM : ∀ ν, Minv (Q (Gc (Qstar ha ac Q ν))) = ν) (hM' : ∀ y, Q (Gc (Qstar ha ac Q (Minv y))) = y)
    (J : Form1 N n) (hJ : ∀ δ, Q δ = 0 → pairForm1 (a : ℂ) J δ = 0) :
    Gt Q (Qstar ha ac Q) Gc Minv J = 0 :=
  Gtilde_J Q (Qstar ha ac Q) Gc Minv (pairForm1 (a : ℂ)) (pairF ac) (pairForm1_nondegenerate ha)
    (pairForm1_symm _) (wpair_symm _) (transpose_spec _ _ _ Q) hGcs hM hM' J hJ

end CriticalConcrete
end CoreLean

end
