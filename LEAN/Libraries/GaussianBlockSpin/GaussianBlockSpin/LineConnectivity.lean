import Mathlib

/-! Connectivity by a list of lines of a multigraph (`ends : E → V × V`): `lineConn ends ls u v` iff `u` and `v` are
joined by a path of lines of `ls` (the reflexive-transitive closure of the endpoint adjacency);
lineConn_append_singleton: adding a line `l` with endpoints `a`, `b` joins exactly the classes of `a` and `b`. -/

namespace GaussianBlockSpin

variable {V E : Type*} (ends : E → V × V)

/-- Two vertices are adjacent through the list of lines. -/
def lineAdj (ls : List E) (u v : V) : Prop := ∃ l ∈ ls, ends l = (u, v) ∨ ends l = (v, u)

/-- Connectivity through the list of lines. -/
def lineConn (ls : List E) : V → V → Prop := Relation.ReflTransGen (lineAdj ends ls)

variable {ends}

lemma lineAdj_symm {ls : List E} {u v : V} (h : lineAdj ends ls u v) : lineAdj ends ls v u := by
  obtain ⟨l, hl, h⟩ := h
  exact ⟨l, hl, h.symm⟩

lemma lineConn_symm {ls : List E} {u v : V} (h : lineConn ends ls u v) : lineConn ends ls v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih => exact Relation.ReflTransGen.head (lineAdj_symm hxy) ih

lemma lineConn_trans {ls : List E} {u v w : V} (h₁ : lineConn ends ls u v) (h₂ : lineConn ends ls v w) :
    lineConn ends ls u w := Relation.ReflTransGen.trans h₁ h₂

lemma lineConn_refl (ls : List E) (u : V) : lineConn ends ls u u := Relation.ReflTransGen.refl

lemma lineConn_mono {ls ls' : List E} (h : ∀ l ∈ ls, l ∈ ls') {u v : V} (hc : lineConn ends ls u v) :
    lineConn ends ls' u v := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
    obtain ⟨l, hl, he⟩ := hxy
    exact ih.tail ⟨l, h l hl, he⟩

lemma lineConn_of_ends {ls : List E} {l : E} (hl : l ∈ ls) : lineConn ends ls (ends l).1 (ends l).2 :=
  Relation.ReflTransGen.single ⟨l, hl, Or.inl rfl⟩

/-- **Adding one line** joins the classes of its endpoints. -/
lemma lineConn_append_singleton (ls : List E) (l : E) (u v : V) :
    lineConn ends (ls ++ [l]) u v ↔ lineConn ends ls u v ∨
      (lineConn ends ls u (ends l).1 ∧ lineConn ends ls (ends l).2 v) ∨
      (lineConn ends ls u (ends l).2 ∧ lineConn ends ls (ends l).1 v) := by
  set a := (ends l).1
  set b := (ends l).2
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (lineConn_refl _ _)
    | @tail x y _ hxy ih =>
      obtain ⟨l', hl', he⟩ := hxy
      rcases List.mem_append.mp hl' with hl' | hl'
      · have hxy : lineConn ends ls x y := Relation.ReflTransGen.single ⟨l', hl', he⟩
        rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl (lineConn_trans h hxy)
        · exact Or.inr (Or.inl ⟨h₁, lineConn_trans h₂ hxy⟩)
        · exact Or.inr (Or.inr ⟨h₁, lineConn_trans h₂ hxy⟩)
      · rw [List.mem_singleton] at hl'
        subst hl'
        have hab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
          rcases he with he | he
          · left; exact ⟨(Prod.ext_iff.mp he).1.symm, (Prod.ext_iff.mp he).2.symm⟩
          · right; exact ⟨(Prod.ext_iff.mp he).2.symm, (Prod.ext_iff.mp he).1.symm⟩
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ih with h | ⟨h₁, _⟩ | ⟨h₁, h₂⟩
          · exact Or.inr (Or.inl ⟨h, lineConn_refl _ _⟩)
          · exact Or.inr (Or.inl ⟨h₁, lineConn_refl _ _⟩)
          · exact Or.inl h₁
        · rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, _⟩
          · exact Or.inr (Or.inr ⟨h, lineConn_refl _ _⟩)
          · exact Or.inl h₁
          · exact Or.inr (Or.inr ⟨h₁, lineConn_refl _ _⟩)
  · have hmono : ∀ {x y : V}, lineConn ends ls x y → lineConn ends (ls ++ [l]) x y :=
      lineConn_mono fun l' hl' => List.mem_append_left _ hl'
    have hab : lineConn ends (ls ++ [l]) a b := lineConn_of_ends (List.mem_append_right _ (List.mem_singleton_self l))
    rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact hmono h
    · exact lineConn_trans (lineConn_trans (hmono h₁) hab) (hmono h₂)
    · exact lineConn_trans (lineConn_trans (hmono h₁) (lineConn_symm hab)) (hmono h₂)

end GaussianBlockSpin
