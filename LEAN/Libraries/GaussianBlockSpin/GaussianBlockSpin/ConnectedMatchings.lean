import GaussianBlockSpin.Matchings

/-! Connected matchings and the first-vertex decomposition. Legs `Fin m` are attached to vertices `Fin n` by `vert`;
a set `B` of vertices is closed under a matching `σ` if `σ` sends the legs of `B` to legs of `B`; `σ` is connected
on `S` if `S` has no nonempty proper closed subset; the component of `v₀` is the intersection of the closed subsets
of `S` containing `v₀`. Main result, sum_matchings_legsOf_eq (the exponential formula behind "cumulants are sums
over connected graphs"): for `v₀ ∈ S`, `M(S) = Σ_{B ⊆ S, v₀ ∈ B} K(B) M(S \ B)` with `M` the sum over all matchings
of the legs and `K` the sum over the connected ones. -/

namespace GaussianBlockSpin

variable {m n : ℕ} (vert : Fin m → Fin n)

/-- The legs attached to the vertices of `B`. -/
def legsOf (B : Finset (Fin n)) : Finset (Fin m) := Finset.univ.filter (fun i => vert i ∈ B)

/-- `B` is closed under `σ`: legs of `B` are sent to legs of `B`. -/
def IsClosedUnder (σ : Equiv.Perm (Fin m)) (B : Finset (Fin n)) : Prop := ∀ i, vert i ∈ B → vert (σ i) ∈ B

instance (σ : Equiv.Perm (Fin m)) (B : Finset (Fin n)) : Decidable (IsClosedUnder vert σ B) := by
  unfold IsClosedUnder; infer_instance

/-- `σ` is connected on `S`: every nonempty closed subset of `S` is `S`. -/
def IsConnectedOn (σ : Equiv.Perm (Fin m)) (S : Finset (Fin n)) : Prop :=
  ∀ B ⊆ S, IsClosedUnder vert σ B → B.Nonempty → B = S

instance (σ : Equiv.Perm (Fin m)) (S : Finset (Fin n)) : Decidable (IsConnectedOn vert σ S) := by
  unfold IsConnectedOn
  exact decidable_of_iff (∀ B ∈ S.powerset, IsClosedUnder vert σ B → B.Nonempty → B = S)
    (by simp only [Finset.mem_powerset])

/-- The component of `v₀` in `S` under `σ`: the vertices of `S` lying in every closed subset of `S` containing `v₀`. -/
def componentOf (σ : Equiv.Perm (Fin m)) (S : Finset (Fin n)) (v₀ : Fin n) : Finset (Fin n) :=
  S.filter (fun u => ∀ B ∈ S.powerset, IsClosedUnder vert σ B → v₀ ∈ B → u ∈ B)

variable {vert}

lemma componentOf_subset (σ : Equiv.Perm (Fin m)) (S : Finset (Fin n)) (v₀ : Fin n) : componentOf vert σ S v₀ ⊆ S :=
  Finset.filter_subset _ _

lemma mem_componentOf_self {σ : Equiv.Perm (Fin m)} {S : Finset (Fin n)} {v₀ : Fin n} (hv₀ : v₀ ∈ S) :
    v₀ ∈ componentOf vert σ S v₀ :=
  Finset.mem_filter.mpr ⟨hv₀, fun _ _ _ h => h⟩

lemma componentOf_subset_of {σ : Equiv.Perm (Fin m)} {S B : Finset (Fin n)} {v₀ : Fin n} (hBS : B ⊆ S)
    (hB : IsClosedUnder vert σ B) (hv₀ : v₀ ∈ B) : componentOf vert σ S v₀ ⊆ B := fun _ hu =>
  (Finset.mem_filter.mp hu).2 B (Finset.mem_powerset.mpr hBS) hB hv₀

lemma isClosedUnder_componentOf {σ : Equiv.Perm (Fin m)} {S : Finset (Fin n)} (hS : IsClosedUnder vert σ S) (v₀ : Fin n) :
    IsClosedUnder vert σ (componentOf vert σ S v₀) := by
  intro i hi
  obtain ⟨hiS, hall⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hS i hiS, fun B hB hBc hv => hBc i (hall B hB hBc hv)⟩

/-- For an involution, the difference of two closed sets is closed. -/
lemma isClosedUnder_sdiff {σ : Equiv.Perm (Fin m)} (hinv : ∀ i, σ (σ i) = i) {A B : Finset (Fin n)}
    (hA : IsClosedUnder vert σ A) (hB : IsClosedUnder vert σ B) : IsClosedUnder vert σ (A \ B) := by
  intro i hi
  obtain ⟨hiA, hiB⟩ := Finset.mem_sdiff.mp hi
  refine Finset.mem_sdiff.mpr ⟨hA i hiA, fun h => hiB ?_⟩
  have := hB (σ i) h
  rwa [hinv] at this

/-- The component of `v₀` is connected. -/
lemma isConnectedOn_componentOf {σ : Equiv.Perm (Fin m)} (hinv : ∀ i, σ (σ i) = i) {S : Finset (Fin n)}
    (hS : IsClosedUnder vert σ S) {v₀ : Fin n} (hv₀ : v₀ ∈ S) : IsConnectedOn vert σ (componentOf vert σ S v₀) := by
  intro B hBc hB hne
  by_cases hv : v₀ ∈ B
  · exact Finset.Subset.antisymm hBc (componentOf_subset_of (hBc.trans (componentOf_subset σ S v₀)) hB hv)
  · exfalso
    have hD := isClosedUnder_sdiff hinv (isClosedUnder_componentOf hS v₀) hB
    have hv₀c : v₀ ∈ componentOf vert σ S v₀ := mem_componentOf_self hv₀
    have hsub := componentOf_subset_of (Finset.sdiff_subset.trans (componentOf_subset σ S v₀)) hD
      (Finset.mem_sdiff.mpr ⟨hv₀c, hv⟩)
    obtain ⟨u, hu⟩ := hne
    have := hsub (hBc hu)
    exact (Finset.mem_sdiff.mp this).2 hu

/-- A matching is an involution of all legs (it fixes the legs outside its set). -/
lemma IsMatching.involutive {s : Finset (Fin m)} {σ : Equiv.Perm (Fin m)} (hσ : IsMatching s σ) (i : Fin m) :
    σ (σ i) = i := by
  by_cases hi : i ∈ s
  · exact (hσ.2 i hi).2.2
  · rw [hσ.1 i hi, hσ.1 i hi]

/-- A matching of the legs of `S` leaves `S` closed. -/
lemma IsMatching.isClosedUnder {S : Finset (Fin n)} {σ : Equiv.Perm (Fin m)} (hσ : IsMatching (legsOf vert S) σ) :
    IsClosedUnder vert σ S := by
  intro i hi
  have hi' : i ∈ legsOf vert S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  exact (Finset.mem_filter.mp (hσ.2 i hi').1).2

/-- The restriction of `σ` to the legs `t` (identity outside `t`), when `σ` preserves `t`; `1` otherwise. -/
def restrictPerm (σ : Equiv.Perm (Fin m)) (t : Finset (Fin m)) : Equiv.Perm (Fin m) :=
  if h : ∀ x, σ x ∈ t ↔ x ∈ t then Equiv.Perm.ofSubtype (σ.subtypePerm h) else 1

lemma restrictPerm_apply_of_mem {σ : Equiv.Perm (Fin m)} {t : Finset (Fin m)} (h : ∀ x, σ x ∈ t ↔ x ∈ t)
    {x : Fin m} (hx : x ∈ t) : restrictPerm σ t x = σ x := by
  rw [restrictPerm, dite_eq_left_of_eq_true (eq_true h), Equiv.Perm.ofSubtype_apply_of_mem _ hx]
  rfl

lemma restrictPerm_apply_of_not_mem {σ : Equiv.Perm (Fin m)} {t : Finset (Fin m)} (h : ∀ x, σ x ∈ t ↔ x ∈ t)
    {x : Fin m} (hx : x ∉ t) : restrictPerm σ t x = x := by
  rw [restrictPerm, dite_eq_left_of_eq_true (eq_true h), Equiv.Perm.ofSubtype_apply_of_not_mem _ hx]

/-- A closed set of vertices gives a `σ`-invariant set of legs (for an involution `σ`). -/
lemma preserves_legsOf {σ : Equiv.Perm (Fin m)} (hinv : ∀ i, σ (σ i) = i) {B : Finset (Fin n)}
    (hB : IsClosedUnder vert σ B) : ∀ x, σ x ∈ legsOf vert B ↔ x ∈ legsOf vert B := by
  intro x
  simp only [legsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have := hB (σ x) h
    rwa [hinv] at this
  · exact hB x

lemma legsOf_mono {B S : Finset (Fin n)} (h : B ⊆ S) : legsOf vert B ⊆ legsOf vert S := fun i hi => by
  simp only [legsOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h hi

lemma mem_legsOf {B : Finset (Fin n)} {i : Fin m} : i ∈ legsOf vert B ↔ vert i ∈ B := by
  simp [legsOf]

/-- The restriction of a matching of the legs of `S` to the legs of a closed `B ⊆ S` is a matching of the legs of `B`. -/
lemma isMatching_restrictPerm {S B : Finset (Fin n)} {σ : Equiv.Perm (Fin m)} (hσ : IsMatching (legsOf vert S) σ)
    (hBS : B ⊆ S) (hB : IsClosedUnder vert σ B) : IsMatching (legsOf vert B) (restrictPerm σ (legsOf vert B)) := by
  have h := preserves_legsOf hσ.involutive hB
  refine ⟨fun x hx => restrictPerm_apply_of_not_mem h hx, fun x hx => ?_⟩
  rw [restrictPerm_apply_of_mem h hx]
  refine ⟨(h x).mpr hx, (hσ.2 x (legsOf_mono hBS hx)).2.1, ?_⟩
  rw [restrictPerm_apply_of_mem h ((h x).mpr hx), hσ.involutive]

/-- Closedness of subsets of `B` depends only on the values on the legs of `B`. -/
lemma isClosedUnder_congr {σ τ : Equiv.Perm (Fin m)} {B B' : Finset (Fin n)} (hB' : B' ⊆ B)
    (hστ : ∀ i ∈ legsOf vert B, σ i = τ i) : IsClosedUnder vert σ B' ↔ IsClosedUnder vert τ B' := by
  constructor
  · intro h i hi
    rw [← hστ i (mem_legsOf.mpr (hB' hi))]
    exact h i hi
  · intro h i hi
    rw [hστ i (mem_legsOf.mpr (hB' hi))]
    exact h i hi

lemma isConnectedOn_congr {σ τ : Equiv.Perm (Fin m)} {B : Finset (Fin n)}
    (hστ : ∀ i ∈ legsOf vert B, σ i = τ i) : IsConnectedOn vert σ B ↔ IsConnectedOn vert τ B := by
  constructor
  · intro h B' hB' hc hne
    exact h B' hB' ((isClosedUnder_congr hB' hστ).mpr hc) hne
  · intro h B' hB' hc hne
    exact h B' hB' ((isClosedUnder_congr hB' hστ).mp hc) hne

lemma legsOf_disjoint_sdiff (B S : Finset (Fin n)) : Disjoint (legsOf vert B) (legsOf vert (S \ B)) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  exact (Finset.mem_sdiff.mp (mem_legsOf.mp hi')).2 (mem_legsOf.mp hi)

lemma legsOf_union_sdiff {B S : Finset (Fin n)} (hBS : B ⊆ S) :
    legsOf vert B ∪ legsOf vert (S \ B) = legsOf vert S := by
  ext i
  simp only [Finset.mem_union, mem_legsOf, Finset.mem_sdiff]
  constructor
  · rintro (h | h)
    · exact hBS h
    · exact h.1
  · intro h
    by_cases hb : vert i ∈ B
    · exact Or.inl hb
    · exact Or.inr ⟨h, hb⟩

/-- Gluing: matchings of the legs of `B` and of `S \ B` multiply to a matching of the legs of `S`, which acts as
the first on the legs of `B` and as the second on the legs of `S \ B`. -/
lemma isMatching_mul {S B : Finset (Fin n)} (hBS : B ⊆ S) {τ₁ τ₂ : Equiv.Perm (Fin m)}
    (h₁ : IsMatching (legsOf vert B) τ₁) (h₂ : IsMatching (legsOf vert (S \ B)) τ₂) :
    IsMatching (legsOf vert S) (τ₁ * τ₂) ∧ (∀ i ∈ legsOf vert B, (τ₁ * τ₂) i = τ₁ i) ∧
      ∀ i ∈ legsOf vert (S \ B), (τ₁ * τ₂) i = τ₂ i := by
  have hd := legsOf_disjoint_sdiff (vert := vert) B S
  have hB : ∀ i ∈ legsOf vert B, (τ₁ * τ₂) i = τ₁ i := fun i hi => by
    rw [Equiv.Perm.mul_apply, h₂.1 i (Finset.disjoint_left.mp hd hi)]
  have hSB : ∀ i ∈ legsOf vert (S \ B), (τ₁ * τ₂) i = τ₂ i := fun i hi => by
    rw [Equiv.Perm.mul_apply, h₁.1 (τ₂ i) (Finset.disjoint_right.mp hd (h₂.2 i hi).1)]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, hB, hSB⟩
  · rw [← legsOf_union_sdiff hBS, Finset.mem_union, not_or] at hi
    rw [Equiv.Perm.mul_apply, h₂.1 i hi.2, h₁.1 i hi.1]
  · rw [← legsOf_union_sdiff hBS, Finset.mem_union] at hi
    rcases hi with hi | hi
    · rw [hB i hi]
      obtain ⟨a1, a2, a3⟩ := h₁.2 i hi
      refine ⟨legsOf_mono hBS a1, a2, ?_⟩
      rw [hB _ a1, a3]
    · rw [hSB i hi]
      obtain ⟨a1, a2, a3⟩ := h₂.2 i hi
      refine ⟨legsOf_mono Finset.sdiff_subset a1, a2, ?_⟩
      rw [hSB _ a1, a3]

/-- The component of `v₀ ∈ B` of a glued matching is `B` when the first factor is connected on `B`. -/
lemma componentOf_mul_eq {S B : Finset (Fin n)} (hBS : B ⊆ S) {τ₁ τ₂ : Equiv.Perm (Fin m)}
    (h₁ : IsMatching (legsOf vert B) τ₁) (h₂ : IsMatching (legsOf vert (S \ B)) τ₂)
    (hc : IsConnectedOn vert τ₁ B) {v₀ : Fin n} (hv₀ : v₀ ∈ B) : componentOf vert (τ₁ * τ₂) S v₀ = B := by
  obtain ⟨hm, hB, -⟩ := isMatching_mul hBS h₁ h₂
  have hBcl : IsClosedUnder vert (τ₁ * τ₂) B := by
    intro i hi
    rw [hB i (mem_legsOf.mpr hi)]
    exact mem_legsOf.mp (h₁.2 i (mem_legsOf.mpr hi)).1
  have hsub := componentOf_subset_of hBS hBcl hv₀
  have hcl := isClosedUnder_componentOf hm.isClosedUnder v₀
  have hcl₁ : IsClosedUnder vert τ₁ (componentOf vert (τ₁ * τ₂) S v₀) := (isClosedUnder_congr hsub hB).mp hcl
  exact hc _ hsub hcl₁ ⟨v₀, mem_componentOf_self (hBS hv₀)⟩

/-- Restricting a glued matching to the legs of `B` (of `S \ B`) gives back the first (second) factor. -/
lemma restrictPerm_mul {S B : Finset (Fin n)} (hBS : B ⊆ S) {τ₁ τ₂ : Equiv.Perm (Fin m)}
    (h₁ : IsMatching (legsOf vert B) τ₁) (h₂ : IsMatching (legsOf vert (S \ B)) τ₂) :
    restrictPerm (τ₁ * τ₂) (legsOf vert B) = τ₁ ∧ restrictPerm (τ₁ * τ₂) (legsOf vert (S \ B)) = τ₂ := by
  obtain ⟨hm, hB, hSB⟩ := isMatching_mul hBS h₁ h₂
  have hpB : ∀ x, (τ₁ * τ₂) x ∈ legsOf vert B ↔ x ∈ legsOf vert B := by
    refine preserves_legsOf hm.involutive fun i hi => ?_
    rw [hB i (mem_legsOf.mpr hi)]
    exact mem_legsOf.mp (h₁.2 i (mem_legsOf.mpr hi)).1
  have hpSB : ∀ x, (τ₁ * τ₂) x ∈ legsOf vert (S \ B) ↔ x ∈ legsOf vert (S \ B) := by
    refine preserves_legsOf hm.involutive fun i hi => ?_
    rw [hSB i (mem_legsOf.mpr hi)]
    exact mem_legsOf.mp (h₂.2 i (mem_legsOf.mpr hi)).1
  constructor
  · ext x
    by_cases hx : x ∈ legsOf vert B
    · rw [restrictPerm_apply_of_mem hpB hx, hB x hx]
    · rw [restrictPerm_apply_of_not_mem hpB hx, h₁.1 x hx]
  · ext x
    by_cases hx : x ∈ legsOf vert (S \ B)
    · rw [restrictPerm_apply_of_mem hpSB hx, hSB x hx]
    · rw [restrictPerm_apply_of_not_mem hpSB hx, h₂.1 x hx]

/-- Gluing the restrictions of a matching of the legs of `S` to a closed `B ⊆ S` and to `S \ B` gives it back. -/
lemma restrictPerm_mul_restrictPerm {S B : Finset (Fin n)} (hBS : B ⊆ S) {σ : Equiv.Perm (Fin m)}
    (hσ : IsMatching (legsOf vert S) σ) (hB : IsClosedUnder vert σ B) :
    restrictPerm σ (legsOf vert B) * restrictPerm σ (legsOf vert (S \ B)) = σ := by
  have hpB := preserves_legsOf hσ.involutive hB
  have hpSB := preserves_legsOf hσ.involutive (isClosedUnder_sdiff hσ.involutive hσ.isClosedUnder hB)
  ext x
  rw [Equiv.Perm.mul_apply]
  by_cases hx : x ∈ legsOf vert (S \ B)
  · rw [restrictPerm_apply_of_mem hpSB hx,
      restrictPerm_apply_of_not_mem hpB (Finset.disjoint_right.mp (legsOf_disjoint_sdiff B S) ((hpSB x).mpr hx))]
  · rw [restrictPerm_apply_of_not_mem hpSB hx]
    by_cases hxB : x ∈ legsOf vert B
    · rw [restrictPerm_apply_of_mem hpB hxB]
    · rw [restrictPerm_apply_of_not_mem hpB hxB]
      have hxS : x ∉ legsOf vert S := by
        rw [← legsOf_union_sdiff hBS, Finset.mem_union]
        tauto
      rw [hσ.1 x hxS]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weight of a glued matching is the product of the weights. -/
lemma matchingWeight_mul (C : E →ₗ[ℝ] E) (w : Fin m → E) {S B : Finset (Fin n)} (hBS : B ⊆ S)
    {τ₁ τ₂ : Equiv.Perm (Fin m)} (h₁ : IsMatching (legsOf vert B) τ₁) (h₂ : IsMatching (legsOf vert (S \ B)) τ₂) :
    matchingWeight C w (legsOf vert S) (τ₁ * τ₂) =
      matchingWeight C w (legsOf vert B) τ₁ * matchingWeight C w (legsOf vert (S \ B)) τ₂ := by
  obtain ⟨-, hB, hSB⟩ := isMatching_mul hBS h₁ h₂
  unfold matchingWeight
  rw [← legsOf_union_sdiff hBS, Finset.filter_union, Finset.prod_union
    (Finset.disjoint_filter_filter (legsOf_disjoint_sdiff B S))]
  congr 1
  · rw [Finset.filter_congr fun i hi => by rw [hB i hi]]
    exact Finset.prod_congr rfl fun i hi => by rw [hB i (Finset.mem_filter.mp hi).1]
  · rw [Finset.filter_congr fun i hi => by rw [hSB i hi]]
    exact Finset.prod_congr rfl fun i hi => by rw [hSB i (Finset.mem_filter.mp hi).1]

/-- **The first-vertex decomposition** (the exponential formula behind cumulants = connected graphs): for
`v₀ ∈ S`, the sum over the matchings of the legs of `S` is
`Σ_{B ⊆ S, v₀ ∈ B} K(B) M(S \ B)`, `K(B)` the sum over the matchings of the legs of `B` connected on `B`, `M` the sum
over all matchings. The bijection sends `σ` to its restrictions to the component of `v₀` and to the rest. -/
theorem sum_matchings_legsOf_eq (C : E →ₗ[ℝ] E) (w : Fin m → E) {S : Finset (Fin n)} {v₀ : Fin n} (hv₀ : v₀ ∈ S) :
    ∑ σ ∈ matchings (legsOf vert S), matchingWeight C w (legsOf vert S) σ =
      ∑ B ∈ S.powerset.filter (fun B => v₀ ∈ B),
        (∑ τ ∈ (matchings (legsOf vert B)).filter (fun τ => IsConnectedOn vert τ B),
            matchingWeight C w (legsOf vert B) τ) *
          ∑ τ ∈ matchings (legsOf vert (S \ B)), matchingWeight C w (legsOf vert (S \ B)) τ := by
  have hmaps : ∀ σ ∈ matchings (legsOf vert S), componentOf vert σ S v₀ ∈ S.powerset.filter (fun B => v₀ ∈ B) :=
    fun σ _ => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (componentOf_subset σ S v₀), mem_componentOf_self hv₀⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBS', hv₀B⟩ := Finset.mem_filter.mp hB
  have hBS := Finset.mem_powerset.mp hBS'
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun σ => (restrictPerm σ (legsOf vert B), restrictPerm σ (legsOf vert (S \ B))))
    (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hσ
    obtain ⟨hm, hc⟩ := hσ
    have hBcl : IsClosedUnder vert σ B := hc ▸ isClosedUnder_componentOf hm.isClosedUnder v₀
    have hpB := preserves_legsOf hm.involutive hBcl
    simp only [Finset.mem_product, Finset.mem_filter, matchings, Finset.mem_univ, true_and]
    refine ⟨⟨isMatching_restrictPerm hm hBS hBcl, ?_⟩,
      isMatching_restrictPerm hm Finset.sdiff_subset (isClosedUnder_sdiff hm.involutive hm.isClosedUnder hBcl)⟩
    have hconn := isConnectedOn_componentOf hm.involutive hm.isClosedUnder hv₀
    rw [hc] at hconn
    exact (isConnectedOn_congr fun i hi => (restrictPerm_apply_of_mem hpB hi).symm).mp hconn
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, matchings, Finset.mem_univ, true_and]
    exact ⟨(isMatching_mul hBS hp.1.1 hp.2).1, componentOf_mul_eq hBS hp.1.1 hp.2 hp.1.2 hv₀B⟩
  · intro σ hσ
    simp only [Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hσ
    obtain ⟨hm, hc⟩ := hσ
    exact restrictPerm_mul_restrictPerm hBS hm (hc ▸ isClosedUnder_componentOf hm.isClosedUnder v₀)
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hp
    obtain ⟨h1, h2⟩ := restrictPerm_mul hBS hp.1.1 hp.2
    exact Prod.ext h1 h2
  · intro σ hσ
    simp only [Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hσ
    obtain ⟨hm, hc⟩ := hσ
    have hBcl : IsClosedUnder vert σ B := hc ▸ isClosedUnder_componentOf hm.isClosedUnder v₀
    have hr1 := isMatching_restrictPerm hm hBS hBcl
    have hr2 := isMatching_restrictPerm hm Finset.sdiff_subset (isClosedUnder_sdiff hm.involutive hm.isClosedUnder hBcl)
    conv_lhs => rw [← restrictPerm_mul_restrictPerm hBS hm hBcl]
    exact matchingWeight_mul C w hBS hr1 hr2

end GaussianBlockSpin
