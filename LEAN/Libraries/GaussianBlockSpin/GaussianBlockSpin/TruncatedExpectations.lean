import GaussianBlockSpin.JointCumulants
import GaussianBlockSpin.Cumulants

/-! The truncated expectations `⟨V^n⟩^T` of I.(3.23) (`truncExp`, Cumulants) as joint cumulants (JointCumulants):
for identical vertices the joint cumulant is `truncExp` of the moments (jointCumulant_eq_truncExp); the joint cumulant
is linear in each vertex (jointCumulant_linear, jointCumulant_sum) and multilinear (jointCumulant_multilinear); hence
`⟨(Σ_a V_a)^n⟩^T = Σ_{g : Fin n → A} κ(V_{g(1)}, …, V_{g(n)})` (truncExp_moments_sum_eq). -/

namespace GaussianBlockSpin

variable {n : ℕ}

/-- The sets `B ⊆ S` containing `v ∈ S` are the sets `insert v B'` with `B' ⊆ S.erase v`. -/
lemma filter_mem_powerset_eq_image {α : Type*} [DecidableEq α] {S : Finset α} {v : α} (hv : v ∈ S) :
    S.powerset.filter (fun B => v ∈ B) = (S.erase v).powerset.image (insert v) := by
  ext B
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hBS, hvB⟩
    exact ⟨B.erase v, Finset.erase_subset_erase v hBS, Finset.insert_erase hvB⟩
  · rintro ⟨B', hB', rfl⟩
    exact ⟨Finset.insert_subset hv (hB'.trans (Finset.erase_subset v S)), Finset.mem_insert_self v B'⟩

/-- Counting the sets through a vertex: `Σ_{B ⊆ S, v ∈ B} f(|B|, |S \ B|) = Σ_{j < |S|} C(|S| - 1, j) f(j + 1, |S| - 1 - j)`. -/
lemma sum_filter_mem_powerset_card {α : Type*} [DecidableEq α] {S : Finset α} {v : α} (hv : v ∈ S)
    (f : ℕ → ℕ → ℝ) :
    ∑ B ∈ S.powerset.filter (fun B => v ∈ B), f B.card (S \ B).card =
      ∑ j ∈ Finset.range S.card, ((S.card - 1).choose j : ℝ) * f (j + 1) (S.card - 1 - j) := by
  have hnot : ∀ B' ∈ (S.erase v).powerset, v ∉ B' := fun B' hB' h => by
    simpa using (Finset.mem_powerset.mp hB') h
  rw [filter_mem_powerset_eq_image hv, Finset.sum_image]
  · have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv
    have h1 : ∀ B' ∈ (S.erase v).powerset, f (insert v B').card (S \ insert v B').card =
        f (B'.card + 1) ((S.erase v).card - B'.card) := by
      intro B' hB'
      have hB'S := Finset.mem_powerset.mp hB'
      rw [Finset.card_insert_of_notMem (hnot B' hB')]
      have : S \ insert v B' = S.erase v \ B' := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [this, Finset.card_sdiff_of_subset hB'S]
    rw [Finset.sum_congr rfl h1, Finset.sum_powerset_apply_card (fun j => f (j + 1) ((S.erase v).card - j)),
      hcard, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨v, hv⟩)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nsmul_eq_mul]
  · intro B1 h1 B2 h2 h
    rw [← Finset.erase_insert (hnot B1 (Finset.mem_coe.mp h1)),
      ← Finset.erase_insert (hnot B2 (Finset.mem_coe.mp h2)), h]

/-- **Joint cumulants of identical vertices are the truncated expectations**: if the moment of a vertex set depends only
on its size, `M(S) = m_{|S|}` with `m_0 = 1`, then `κ(S) = ⟨V^{|S|}⟩^T` (`truncExp`, I.(3.23)) for nonempty `S`. -/
theorem jointCumulant_eq_truncExp (m : ℕ → ℝ) (hm0 : m 0 = 1) (S : Finset (Fin n)) (h : S.Nonempty) :
    jointCumulant (fun S => m S.card) S = truncExp m S.card := by
  refine (eq_jointCumulant_of_decomp (fun S => m S.card) (fun B => truncExp m B.card) hm0 (fun S h => ?_) S h).symm
  have hS : S.card = S.card - 1 + 1 := (Nat.sub_add_cancel (Finset.card_pos.mpr h)).symm
  rw [sum_filter_mem_powerset_card (S.min'_mem h) (fun j k => truncExp m j * m k)]
  conv_lhs => rw [hS, moment_succ_eq m hm0 (S.card - 1), ← hS]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Linearity of the joint cumulant in one vertex**: if the moments of the sets containing `u` are
`M = a M₁ + b M₂`, and the moments of the sets avoiding `u` agree, then `κ(S) = a κ₁(S) + b κ₂(S)` for `u ∈ S`, and
`κ(S) = κ₁(S) = κ₂(S)` for `u ∉ S`. -/
theorem jointCumulant_linear (M M₁ M₂ : Finset (Fin n) → ℝ) (u : Fin n) (a b : ℝ)
    (hout : ∀ T, u ∉ T → M₁ T = M T ∧ M₂ T = M T) (hin : ∀ T, u ∈ T → M T = a * M₁ T + b * M₂ T)
    (S : Finset (Fin n)) :
    (u ∈ S → jointCumulant M S = a * jointCumulant M₁ S + b * jointCumulant M₂ S) ∧
      (u ∉ S → jointCumulant M₁ S = jointCumulant M S ∧ jointCumulant M₂ S = jointCumulant M S) := by
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
    by_cases h : S.Nonempty
    swap
    · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst hS
      refine ⟨fun hu => absurd hu (Finset.notMem_empty u), fun _ => ?_⟩
      simp [jointCumulant]
    rw [jointCumulant_of_nonempty M h, jointCumulant_of_nonempty M₁ h, jointCumulant_of_nonempty M₂ h]
    have hB : ∀ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B),
        (u ∈ B → jointCumulant M B = a * jointCumulant M₁ B + b * jointCumulant M₂ B) ∧
          (u ∉ B → jointCumulant M₁ B = jointCumulant M B ∧ jointCumulant M₂ B = jointCumulant M B) :=
      fun B hB => ih B.card (hc ▸ card_lt_of_mem_proper (Finset.mem_filter.mp hB).1) B rfl
    constructor
    · intro hu
      have hterm : ∀ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B),
          jointCumulant M B * M (S \ B) =
            a * (jointCumulant M₁ B * M₁ (S \ B)) + b * (jointCumulant M₂ B * M₂ (S \ B)) := by
        intro B hBm
        by_cases huB : u ∈ B
        · have hsd : u ∉ S \ B := fun hh => (Finset.mem_sdiff.mp hh).2 huB
          rw [(hB B hBm).1 huB, (hout _ hsd).1, (hout _ hsd).2]
          ring
        · have hsd : u ∈ S \ B := Finset.mem_sdiff.mpr ⟨hu, huB⟩
          rw [hin _ hsd, ((hB B hBm).2 huB).1, ((hB B hBm).2 huB).2]
          ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hin S hu]
      ring
    · intro hu
      have hterm1 : ∀ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => S.min' h ∈ B),
          jointCumulant M₁ B * M₁ (S \ B) = jointCumulant M B * M (S \ B) ∧
            jointCumulant M₂ B * M₂ (S \ B) = jointCumulant M B * M (S \ B) := by
        intro B hBm
        have huB : u ∉ B := fun hh => hu
          (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hBm).1).1 hh)
        have hsd : u ∉ S \ B := fun hh => hu (Finset.mem_sdiff.mp hh).1
        rw [((hB B hBm).2 huB).1, ((hB B hBm).2 huB).2, (hout _ hsd).1, (hout _ hsd).2]
        exact ⟨rfl, rfl⟩
      rw [Finset.sum_congr rfl (fun B hBm => (hterm1 B hBm).1), Finset.sum_congr rfl (fun B hBm => (hterm1 B hBm).2),
        (hout S hu).1, (hout S hu).2]
      exact ⟨rfl, rfl⟩

/-- **Additivity in one vertex**: if the moments of the sets containing `u` are `M = Σ_{a ∈ s} M_a`, and each `M_a`
agrees with `M` on the sets avoiding `u`, then `κ(S) = Σ_{a ∈ s} κ_a(S)` for `u ∈ S`. -/
theorem jointCumulant_sum {A : Type*} [DecidableEq A] (s : Finset A) (u : Fin n) :
    ∀ (M : Finset (Fin n) → ℝ) (Ma : A → Finset (Fin n) → ℝ), (∀ a T, u ∉ T → Ma a T = M T) →
      (∀ T, u ∈ T → M T = ∑ a ∈ s, Ma a T) → ∀ S : Finset (Fin n), u ∈ S →
        jointCumulant M S = ∑ a ∈ s, jointCumulant (Ma a) S := by
  induction s using Finset.induction_on with
  | empty =>
    intro M Ma _ hin S hu
    have h := (jointCumulant_linear M M M u 0 0 (fun T _ => ⟨rfl, rfl⟩)
      (fun T hT => by rw [hin T hT]; simp) S).1 hu
    rw [h]
    simp
  | insert a s ha ih =>
    intro M Ma hout hin S hu
    let M' : Finset (Fin n) → ℝ := fun T => if u ∈ T then ∑ b ∈ s, Ma b T else M T
    have h1 := (jointCumulant_linear M (Ma a) M' u 1 1
      (fun T hT => ⟨hout a T hT, by simp [M', hT]⟩)
      (fun T hT => by rw [hin T hT, Finset.sum_insert ha]; simp [M', hT]) S).1 hu
    have h2 := ih M' Ma (fun b T hT => by simp [M', hT, hout b T hT]) (fun T hT => by simp [M', hT]) S hu
    rw [h1, h2, Finset.sum_insert ha]
    ring

/-- **Multilinearity of the joint cumulant**: let `M f` be moment functions indexed by partial choices
`f : Fin n → Option A` (`f v = none`: vertex `v` is the full sum; `f v = some a`: vertex `v` is its `a`-th piece), with
additivity in each unexpanded vertex and locality. Then the joint cumulant of all vertices with nothing expanded is the
sum over all full choices `g : Fin n → A` of the joint cumulants of the pieces. -/
theorem jointCumulant_multilinear {A : Type*} [Fintype A] [DecidableEq A]
    (M : (Fin n → Option A) → Finset (Fin n) → ℝ)
    (hsum : ∀ f u, f u = none → ∀ T, u ∈ T → M f T = ∑ a, M (Function.update f u (some a)) T)
    (hloc : ∀ f u, f u = none → ∀ a T, u ∉ T → M (Function.update f u (some a)) T = M f T) :
    jointCumulant (M fun _ => none) Finset.univ =
      ∑ g : Fin n → A, jointCumulant (M fun v => some (g v)) Finset.univ := by
  have key : ∀ U : Finset (Fin n), ∀ f : Fin n → Option A, (∀ v, f v = none ↔ v ∈ U) →
      jointCumulant (M f) Finset.univ =
        ∑ g ∈ Finset.univ.filter (fun g : Fin n → A => ∀ v, v ∉ U → f v = some (g v)),
          jointCumulant (M fun v => some (g v)) Finset.univ := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro f hf
      have hsome : ∀ v, ∃ a, f v = some a := fun v => by
        cases hfv : f v with
        | none => exact absurd ((hf v).mp hfv) (Finset.notMem_empty v)
        | some a => exact ⟨a, rfl⟩
      choose g0 hg0 using hsome
      have hfil : Finset.univ.filter (fun g : Fin n → A => ∀ v, v ∉ (∅ : Finset (Fin n)) → f v = some (g v)) =
          {g0} := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, not_false_eq_true,
          forall_const, Finset.mem_singleton]
        constructor
        · intro h
          funext v
          have := (hg0 v).symm.trans (h v)
          exact (Option.some_injective A this).symm
        · rintro rfl v
          exact hg0 v
      rw [hfil, Finset.sum_singleton]
      have : (fun v => some (g0 v)) = f := funext fun v => (hg0 v).symm
      rw [this]
    | insert u U hu ih =>
      intro f hf
      have hfu : f u = none := (hf u).mpr (Finset.mem_insert_self u U)
      rw [jointCumulant_sum Finset.univ u (M f) (fun a => M (Function.update f u (some a)))
        (fun a T hT => hloc f u hfu a T hT) (fun T hT => hsum f u hfu T hT) Finset.univ (Finset.mem_univ u)]
      have hfa : ∀ a, ∀ v, Function.update f u (some a) v = none ↔ v ∈ U := by
        intro a v
        by_cases hv : v = u
        · subst hv
          simp [hu]
        · rw [Function.update_of_ne hv, hf v, Finset.mem_insert]
          simp [hv]
      simp_rw [fun a => ih (Function.update f u (some a)) (hfa a)]
      rw [← Finset.sum_fiberwise (Finset.univ.filter (fun g : Fin n → A => ∀ v, v ∉ insert u U → f v = some (g v)))
        (fun g => g u)]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
      constructor
      · intro h
        have hgu : g u = a := by
          have := h u hu
          rw [Function.update_self] at this
          exact (Option.some_injective A this).symm
        refine ⟨fun v ⟨hvu, hvU⟩ => ?_, hgu⟩
        have := h v hvU
        rwa [Function.update_of_ne hvu] at this
      · rintro ⟨h, hgu⟩ v hvU
        by_cases hvu : v = u
        · subst hvu
          rw [Function.update_self, hgu]
        · rw [Function.update_of_ne hvu]
          exact h v ⟨hvu, hvU⟩
  have h := key Finset.univ (fun _ => none) (fun v => by simp)
  rw [h]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext g
  simp

open MeasureTheory in
/-- **Truncated expectations of a sum are sums of joint cumulants of its pieces**: for `V = Σ_{a ∈ A} V_a` under a
probability measure (all products of partial sums of the pieces integrable),
`⟨V^n⟩^T = Σ_{g : Fin n → A} κ(V_{g(1)}, …, V_{g(n)})`, the joint cumulant of the moment function
`T ↦ ⟨∏_{v ∈ T} V_{g(v)}⟩` (I.(3.23)). -/
theorem truncExp_moments_sum_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Type*} [Fintype A] [DecidableEq A] (V : A → Ω → ℝ)
    (hint : ∀ (T : Finset (Fin n)) (t : Fin n → Finset A), Integrable (fun ω => ∏ v ∈ T, ∑ a ∈ t v, V a ω) μ)
    (hn : 0 < n) :
    truncExp (moments μ (fun ω => ∑ a, V a ω)) n =
      ∑ g : Fin n → A, jointCumulant (fun T => ∫ ω, ∏ v ∈ T, V (g v) ω ∂μ) Finset.univ := by
  let tf : (Fin n → Option A) → Fin n → Finset A := fun f v => (f v).elim Finset.univ (fun a => {a})
  let M : (Fin n → Option A) → Finset (Fin n) → ℝ := fun f T => ∫ ω, ∏ v ∈ T, ∑ a ∈ tf f v, V a ω ∂μ
  have hupd : ∀ f u a, tf (Function.update f u (some a)) u = {a} := fun f u a => by
    simp [tf]
  have hupd' : ∀ f u a v, v ≠ u → tf (Function.update f u (some a)) v = tf f v := fun f u a v hv => by
    simp [tf, Function.update_of_ne hv]
  have hsum : ∀ f u, f u = none → ∀ T, u ∈ T → M f T = ∑ a, M (Function.update f u (some a)) T := by
    intro f u hfu T hu
    have hpt : ∀ ω, ∏ v ∈ T, ∑ b ∈ tf f v, V b ω =
        ∑ a, ∏ v ∈ T, ∑ b ∈ tf (Function.update f u (some a)) v, V b ω := by
      intro ω
      rw [← Finset.mul_prod_erase T _ hu]
      have htu : tf f u = Finset.univ := by simp [tf, hfu]
      rw [htu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_prod_erase T _ hu, hupd, Finset.sum_singleton]
      congr 1
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [hupd' f u a v (Finset.ne_of_mem_erase hv)]
    simp only [M]
    simp_rw [hpt]
    exact integral_finsetSum _ fun a _ => hint T _
  have hloc : ∀ f u, f u = none → ∀ a T, u ∉ T → M (Function.update f u (some a)) T = M f T := by
    intro f u _ a T hu
    simp only [M]
    congr 1
    funext ω
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hupd' f u a v (fun h => hu (h ▸ hv))]
  have hml := jointCumulant_multilinear M hsum hloc
  have hnone : M (fun _ => none) = fun T => moments μ (fun ω => ∑ a, V a ω) T.card := by
    funext T
    simp [M, tf, moments, Finset.prod_const]
  have hsome : ∀ g : Fin n → A, M (fun v => some (g v)) = fun T => ∫ ω, ∏ v ∈ T, V (g v) ω ∂μ := by
    intro g
    funext T
    simp [M, tf]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hnone, jointCumulant_eq_truncExp _ (moments_zero μ _) Finset.univ Finset.univ_nonempty,
    Finset.card_univ, Fintype.card_fin] at hml
  rw [hml]
  exact Finset.sum_congr rfl fun g _ => by rw [hsome g]

end GaussianBlockSpin
