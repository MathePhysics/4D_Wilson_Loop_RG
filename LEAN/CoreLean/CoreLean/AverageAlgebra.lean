/-
`lem:average`(i) and (iii) of BALABAN_CORE.tex (stated there without proof), the algebra of the average.

`def:average`: for a coarse bond `c`, a point `x ∈ B(c₋)` (the index type `ι`, with `|ι| = L⁴`), paths
`Γ ∈ 𝐆(c₋, x)` (the type `P x`) and `Γ' ∈ 𝐆(c₊, x')` (the type `P' x`), the loop
`ℓ_c(x, Γ, Γ') = Γ · [x, x'] · Γ'⁻¹ · [c]⁻¹` has the holonomy `U(Γ)U([x, x'])U(Γ')⁻¹U([c])⁻¹` (`loop`, with the
transports `g`, `h`, `g'`, `k` of the four paths). With the weights `w_x = (L⁴|𝐆(c₋, x)||𝐆(c₊, x')|)⁻¹`,
`β_c(U) = Σ w_x (1/i) log U(ℓ_c(x, Γ, Γ'))` (`beta`), and `M(U)(c) = e^{iβ_c(U)}U([c])` if every loop lies in
`N_G`, `U([c])` otherwise (`avg`).

The logarithm enters as a named input: a function `log` on a set `N_G` of group elements with
`log(gWg⁻¹) = Ad_g log W` for `g` in a subgroup `S` (the group `G`, whose conjugations preserve `N_G`) and
`log(W⁻¹) = -log W`.

* `avg_covariant` (`lem:average`(iii)): under a gauge transformation `u` with values in `S`, the transports
  change by `u` at their ends, every loop is conjugated by `u(c₋)`, `β_c` by `Ad_{u(c₋)}`, and
  `M(U^u)(c) = u(c₋)M(U)(c)u(c₊)⁻¹`.
* `avg_reverse` (`lem:average`(i)): for the reversed bond `c⁻¹` the paths of the two blocks are exchanged and
  `[x', x] = [x, x']⁻¹`, `[c⁻¹] = [c]⁻¹`; the loops of `c⁻¹` are `U([c])⁻¹U(ℓ_c)⁻¹U([c])`, so
  `β_{c⁻¹} = -Ad_{U([c])⁻¹}β_c` and `M(U)(c⁻¹) = M(U)(c)⁻¹`, when `U([c]) ∈ S`.
-/
import CoreLean.Differences

open Matrix Complex
open scoped Classical

noncomputable section

namespace CoreLean

namespace Average

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {ι : Type*} [Fintype ι] {P P' : ι → Type*} [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)]

/-- The holonomy of the loop `ℓ_c(x, Γ, Γ') = Γ · [x, x'] · Γ'⁻¹ · [c]⁻¹`. -/
def loop (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN) (k : GLN) (x : ι) (Γ : P x)
    (Γ' : P' x) : GLN :=
  g x Γ * h x * (g' x Γ')⁻¹ * k⁻¹

/-- The weight `(L⁴|𝐆(c₋, x)||𝐆(c₊, x')|)⁻¹`. -/
def wt (P P' : ι → Type*) [∀ x, Fintype (P x)] [∀ x, Fintype (P' x)] (x : ι) : ℂ :=
  ((Fintype.card ι : ℂ) * Fintype.card (P x) * Fintype.card (P' x))⁻¹

/-- `β_c(U) = Σ_x w_x Σ_{Γ, Γ'} (1/i) log U(ℓ_c(x, Γ, Γ'))` (`eq:average-exponent`). -/
def beta (log : GLN → Mat) (g : ∀ x, P x → GLN) (h : ι → GLN) (g' : ∀ x, P' x → GLN) (k : GLN) : Mat :=
  ∑ x, ∑ Γ, ∑ Γ', wt P P' x • ((1 / I : ℂ) • log (loop g h g' k x Γ Γ'))

/-- `M(U)(c)` (`eq:average`). -/
def avg (inN : GLN → Prop) (log : GLN → Mat) (g : ∀ x, P x → GLN) (h : ι → GLN)
    (g' : ∀ x, P' x → GLN) (k : GLN) : GLN :=
  if ∀ x Γ Γ', inN (loop g h g' k x Γ Γ') then expU (I • beta log g h g' k) * k else k

lemma Ad_sum {α : Type*} (s : Finset α) (W : GLN) (f : α → Mat) :
    Ad W (∑ a ∈ s, f a) = ∑ a ∈ s, Ad W (f a) := by
  simp only [Ad, Finset.mul_sum, Finset.sum_mul]

/-- The named input on the logarithm. -/
structure LogInput (S : Subgroup GLN) (inN : GLN → Prop) (log : GLN → Mat) : Prop where
  conj : ∀ g ∈ S, ∀ W, inN W → inN (g * W * g⁻¹) ∧ log (g * W * g⁻¹) = Ad g (log W)
  inv : ∀ W, inN W → inN W⁻¹ ∧ log W⁻¹ = -log W

variable {S : Subgroup (Matrix (Fin N) (Fin N) ℂ)ˣ} {inN : (Matrix (Fin N) (Fin N) ℂ)ˣ → Prop}
  {log : (Matrix (Fin N) (Fin N) ℂ)ˣ → Matrix (Fin N) (Fin N) ℂ}

lemma LogInput.conj_iff (hL : LogInput S inN log) {g : GLN} (hg : g ∈ S) (W : GLN) :
    inN (g * W * g⁻¹) ↔ inN W := by
  refine ⟨fun h => ?_, fun h => (hL.conj g hg W h).1⟩
  have := (hL.conj g⁻¹ (S.inv_mem hg) _ h).1
  rwa [show g⁻¹ * (g * W * g⁻¹) * g⁻¹⁻¹ = W by group] at this

lemma LogInput.inv_iff (hL : LogInput S inN log) (W : GLN) : inN W⁻¹ ↔ inN W := by
  refine ⟨fun h => ?_, fun h => (hL.inv W h).1⟩
  have := (hL.inv _ h).1
  rwa [inv_inv] at this

/-- `lem:average`(iii): `M(U^u)(c) = u(c₋)M(U)(c)u(c₊)⁻¹` for a gauge transformation with values in `S`. -/
theorem avg_covariant (hL : LogInput S inN log) (g : ∀ x, P x → GLN) (h : ι → GLN)
    (g' : ∀ x, P' x → GLN) (k : GLN) (um up : GLN) (hum : um ∈ S) (ux ux' : ι → GLN) :
    avg inN log (fun x Γ => um * g x Γ * (ux x)⁻¹) (fun x => ux x * h x * (ux' x)⁻¹)
        (fun x Γ' => up * g' x Γ' * (ux' x)⁻¹) (um * k * up⁻¹) =
      um * avg inN log g h g' k * up⁻¹ := by
  -- the loops are conjugated by `u(c₋)`
  have hloop : ∀ x Γ Γ', loop (fun x Γ => um * g x Γ * (ux x)⁻¹) (fun x => ux x * h x * (ux' x)⁻¹)
      (fun x Γ' => up * g' x Γ' * (ux' x)⁻¹) (um * k * up⁻¹) x Γ Γ' =
      um * loop g h g' k x Γ Γ' * um⁻¹ := fun x Γ Γ' => by
    simp only [loop]; group
  unfold avg
  simp only [hloop, hL.conj_iff hum]
  split_ifs with hN
  · -- `β_c(U^u) = Ad_{u(c₋)}β_c(U)`
    have hb : beta log (fun x Γ => um * g x Γ * (ux x)⁻¹) (fun x => ux x * h x * (ux' x)⁻¹)
        (fun x Γ' => up * g' x Γ' * (ux' x)⁻¹) (um * k * up⁻¹) = Ad um (beta log g h g' k) := by
      simp only [beta, hloop, Ad_sum, Ad_smul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Γ _ =>
        Finset.sum_congr rfl fun Γ' _ => ?_
      rw [(hL.conj um hum _ (hN x Γ Γ')).2]
    rw [hb, ← Ad_smul, ← expU_conj]
    group
  · group

/-- `lem:average`(i): `M(U)(c⁻¹) = M(U)(c)⁻¹`, when `U([c]) ∈ S`. For `c⁻¹` the paths of the two blocks are
exchanged, `[x', x] = [x, x']⁻¹`, and `[c⁻¹] = [c]⁻¹`; the weights are the same. -/
theorem avg_reverse (hL : LogInput S inN log) (g : ∀ x, P x → GLN) (h : ι → GLN)
    (g' : ∀ x, P' x → GLN) (k : GLN) (hk : k ∈ S) :
    avg inN log g' (fun x => (h x)⁻¹) g k⁻¹ = (avg inN log g h g' k)⁻¹ := by
  -- the loops of `c⁻¹` are `U([c])⁻¹U(ℓ_c)⁻¹U([c])`
  have hloop : ∀ x (Γ' : P' x) (Γ : P x), loop g' (fun x => (h x)⁻¹) g k⁻¹ x Γ' Γ =
      k⁻¹ * (loop g h g' k x Γ Γ')⁻¹ * k⁻¹⁻¹ := fun x Γ' Γ => by
    simp only [loop]; group
  have hkS : k⁻¹ ∈ S := S.inv_mem hk
  unfold avg
  simp only [hloop, hL.conj_iff hkS, hL.inv_iff]
  have hNiff : (∀ x (Γ' : P' x) (Γ : P x), inN (loop g h g' k x Γ Γ')) ↔
      ∀ x (Γ : P x) (Γ' : P' x), inN (loop g h g' k x Γ Γ') :=
    ⟨fun H x Γ Γ' => H x Γ' Γ, fun H x Γ' Γ => H x Γ Γ'⟩
  by_cases hN : ∀ x (Γ : P x) (Γ' : P' x), inN (loop g h g' k x Γ Γ')
  swap
  · rw [if_neg (fun H => hN (hNiff.mp H)), if_neg hN]
  rw [if_pos (hNiff.mpr hN), if_pos hN]
  · -- `β_{c⁻¹} = -Ad_{U([c])⁻¹}β_c`
    have hw : ∀ x, wt P' P x = wt P P' x := fun x => by simp only [wt]; ring
    have hb : beta log g' (fun x => (h x)⁻¹) g k⁻¹ = -Ad k⁻¹ (beta log g h g' k) := by
      simp only [beta, hloop, hw, Ad_sum, Ad_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Γ _ => Finset.sum_congr rfl fun Γ' _ => ?_
      have hN' := (hL.inv _ (hN x Γ Γ')).1
      rw [(hL.conj k⁻¹ hkS _ hN').2, (hL.inv _ (hN x Γ Γ')).2, Ad_neg, smul_neg, smul_neg]
    rw [hb, smul_neg, ← Ad_smul, ← Ad_neg, ← expU_conj, ← expU_inv]
    group

end Average

end CoreLean
