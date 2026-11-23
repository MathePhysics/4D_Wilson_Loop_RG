/-
`lem:problem-covariance` of BALABAN_CORE.tex (`a021c13be348`), in abstract form. A group `𝒢` (the gauge
transformations of `T^{(0)}`) acts on the configurations, on the data (`V^u(c) = u(c₋)V(c)u(c₊)⁻¹`), and on the
`1`-forms (`Ad_u`). The inputs are the facts which the core's proof cites: the action `A` and the set `𝔘(ε₀)` are
invariant (`lem:action`(ii), `eq:current-covariance`), `U ∈ 𝔙(V) ⟺ U^u ∈ 𝔙(V^u)` (`lem:average`(iii)), the regularity
of the data is invariant, `δA ∈ ker Q(U) ⟺ Ad_uδA ∈ ker Q(U^u)` (`prop:relative-average-order`(v)), and
`⟨Ad_uδA, J(U^u)⟩ = ⟨δA, J(U)⟩` (`eq:current-covariance` and the invariance of the trace). Then `U ↦ U^u` is a
bijection of `𝔘(ε₀) ∩ 𝔙(V)` onto `𝔘(ε₀) ∩ 𝔙(V^u)` (`bijOn`) preserving the action, minimality (`minimal_smul`),
and criticality (`critical_smul`), and for `u` fixing the data (`𝒢_𝐁`) the critical and minimal configurations
form unions of orbits (`orbits`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ProblemCov

/-- The setting: the action of `𝒢` on the configurations `C`, the data `D`, and the forms `T`, with the action `S`,
the set `Ureg = 𝔘(ε₀)`, the constraint sets `Vset V = 𝔙(V)`, the regularity `Reg` of the data, the kernels
`K U = ker Q(U)`, and the pairings `ℓ U δ = ⟨δ, J(U)⟩`. -/
structure Setting (𝒢 C D T : Type*) [Group 𝒢] [MulAction 𝒢 C] [MulAction 𝒢 D] [MulAction 𝒢 T] where
  S : C → ℝ
  Ureg : Set C
  Vset : D → Set C
  Reg : D → Prop
  K : C → Set T
  ℓ : C → T → ℝ
  S_inv : ∀ (u : 𝒢) U, S (u • U) = S U
  U_inv : ∀ (u : 𝒢) U, u • U ∈ Ureg ↔ U ∈ Ureg
  V_cov : ∀ (u : 𝒢) V U, u • U ∈ Vset (u • V) ↔ U ∈ Vset V
  Reg_inv : ∀ (u : 𝒢) V, Reg (u • V) ↔ Reg V
  K_cov : ∀ (u : 𝒢) U δ, u • δ ∈ K (u • U) ↔ δ ∈ K U
  ℓ_cov : ∀ (u : 𝒢) U δ, ℓ (u • U) (u • δ) = ℓ U δ

namespace Setting

variable {𝒢 C D T : Type*} [Group 𝒢] [MulAction 𝒢 C] [MulAction 𝒢 D] [MulAction 𝒢 T]
variable (P : Setting 𝒢 C D T)

/-- `U` is minimal in `𝔘(ε₀) ∩ 𝔙(V)`. -/
def Minimal (V : D) (U : C) : Prop := U ∈ P.Ureg ∩ P.Vset V ∧ ∀ U' ∈ P.Ureg ∩ P.Vset V, P.S U ≤ P.S U'

/-- `U` is critical: `⟨δA, J(U)⟩ = 0` for `δA ∈ ker Q(U)`. -/
def Critical (U : C) : Prop := ∀ δ ∈ P.K U, P.ℓ U δ = 0

lemma mem_iff (u : 𝒢) (V : D) (U : C) :
    u • U ∈ P.Ureg ∩ P.Vset (u • V) ↔ U ∈ P.Ureg ∩ P.Vset V := by
  simp only [Set.mem_inter_iff, P.U_inv, P.V_cov]

/-- `U ↦ U^u` is a bijection of `𝔘(ε₀) ∩ 𝔙(V)` onto `𝔘(ε₀) ∩ 𝔙(V^u)`. -/
theorem bijOn (u : 𝒢) (V : D) :
    Set.BijOn (fun U => u • U) (P.Ureg ∩ P.Vset V) (P.Ureg ∩ P.Vset (u • V)) := by
  refine ⟨fun U hU => (P.mem_iff u V U).2 hU, fun U _ U' _ h => smul_left_cancel u h, fun U hU => ?_⟩
  refine ⟨u⁻¹ • U, (P.mem_iff u V _).1 ?_, by simp⟩
  rwa [smul_inv_smul]

/-- Minimal configurations are mapped to minimal ones. -/
theorem minimal_smul (u : 𝒢) {V : D} {U : C} (h : P.Minimal V U) : P.Minimal (u • V) (u • U) := by
  refine ⟨(P.mem_iff u V U).2 h.1, fun U' hU' => ?_⟩
  have h1 : u⁻¹ • U' ∈ P.Ureg ∩ P.Vset V := (P.mem_iff u V _).1 (by rwa [smul_inv_smul])
  have h2 := h.2 _ h1
  rw [P.S_inv]
  have h3 : P.S (u⁻¹ • U') = P.S U' := P.S_inv _ _
  linarith

/-- Critical configurations are mapped to critical ones. -/
theorem critical_smul (u : 𝒢) {U : C} (h : P.Critical U) : P.Critical (u • U) := by
  intro δ hδ
  have h1 : u⁻¹ • δ ∈ P.K U := (P.K_cov u U _).1 (by rwa [smul_inv_smul])
  have := P.ℓ_cov u U (u⁻¹ • δ)
  rw [smul_inv_smul] at this
  rw [this]; exact h _ h1

/-- The regularity of the data is preserved. -/
theorem reg_smul (u : 𝒢) {V : D} (h : P.Reg V) : P.Reg (u • V) := (P.Reg_inv u V).2 h

/-- For `u` fixing the data (`u ∈ 𝒢_𝐁`), the critical and the minimal configurations of `𝔘(ε₀) ∩ 𝔙(V)` form unions
of orbits. -/
theorem orbits (u : 𝒢) {V : D} (hV : u • V = V) {U : C} :
    (P.Minimal V U → P.Minimal V (u • U)) ∧
      (U ∈ P.Ureg ∩ P.Vset V → P.Critical U → u • U ∈ P.Ureg ∩ P.Vset V ∧ P.Critical (u • U)) := by
  refine ⟨fun h => hV ▸ P.minimal_smul u h, fun hU hc => ⟨?_, P.critical_smul u hc⟩⟩
  have := (P.mem_iff u V U).2 hU
  rwa [hV] at this

end Setting
end ProblemCov
end CoreLean

end
