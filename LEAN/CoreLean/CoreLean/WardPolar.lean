/-
`lem:ward`: polarisation of symmetric biadditive and triadditive forms with values in `ℂ`, on a set of
vectors closed under addition (the fields with values in `𝔤^c`).
-/
import Mathlib

namespace CoreLean

namespace Ward

/-- Polarisation of a symmetric biadditive form. -/
lemma polar2 {V : Type*} [AddCommGroup V] (P : V → Prop) (Φ : V → V → ℂ)
    (add1 : ∀ x x' y, Φ (x + x') y = Φ x y + Φ x' y) (s12 : ∀ x y, Φ x y = Φ y x)
    (hP : ∀ x y, P x → P y → P (x + y)) (hdiag : ∀ x, P x → Φ x x = 0)
    {x y : V} (hx : P x) (hy : P y) : Φ x y = 0 := by
  have add2 : ∀ x y y', Φ x (y + y') = Φ x y + Φ x y' := fun x y y' => by
    rw [s12, add1, s12 y, s12 y']
  have h := hdiag (x + y) (hP x y hx hy)
  have h1 := hdiag x hx
  have h2 := hdiag y hy
  rw [add1, add2, add2, s12 y x] at h
  linear_combination (h - h1 - h2) / 2

/-- Polarisation of a symmetric triadditive form. -/
lemma polar3 {V : Type*} [AddCommGroup V] (P : V → Prop) (Φ : V → V → V → ℂ)
    (add1 : ∀ x x' y z, Φ (x + x') y z = Φ x y z + Φ x' y z)
    (s12 : ∀ x y z, Φ x y z = Φ y x z) (s23 : ∀ x y z, Φ x y z = Φ x z y)
    (hP : ∀ x y, P x → P y → P (x + y)) (hdiag : ∀ x, P x → Φ x x x = 0)
    {x y z : V} (hx : P x) (hy : P y) (hz : P z) : Φ x y z = 0 := by
  have add2 : ∀ x y y' z, Φ x (y + y') z = Φ x y z + Φ x y' z := fun x y y' z => by
    rw [s12, add1, s12 y, s12 y']
  have add3 : ∀ x y z z', Φ x y (z + z') = Φ x y z + Φ x y z' := fun x y z z' => by
    rw [s23, add2, s23 x z, s23 x z']
  have h7 := hdiag (x + y + z) (hP _ _ (hP _ _ hx hy) hz)
  have hxy := hdiag (x + y) (hP _ _ hx hy)
  have hxz := hdiag (x + z) (hP _ _ hx hz)
  have hyz := hdiag (y + z) (hP _ _ hy hz)
  have h1 := hdiag x hx
  have h2 := hdiag y hy
  have h3 := hdiag z hz
  simp only [add1, add2, add3] at h7 hxy hxz hyz
  -- all orderings of the arguments, in terms of `Φ x y z`, `Φ x x y`, …
  have p1 : Φ x z y = Φ x y z := (s23 x y z).symm
  have p2 : Φ y x z = Φ x y z := (s12 x y z).symm
  have p4 : Φ z x y = Φ x y z := (s12 z x y).trans (s23 x z y)
  have p3 : Φ y z x = Φ x y z := (s12 y z x).trans ((s23 z y x).trans p4)
  have p5 : Φ z y x = Φ x y z := (s23 z y x).trans p4
  have q1 : ∀ u v, Φ u v u = Φ u u v := fun u v => (s23 u u v).symm
  have q2 : ∀ u v, Φ v u u = Φ u u v := fun u v => (s12 v u u).trans (s23 u v u)
  rw [p1, p2, p3, p4, p5, q1 x y, q1 x z, q1 y x, q1 y z, q1 z x, q1 z y, q2 x y, q2 x z, q2 y x,
    q2 y z, q2 z x, q2 z y] at h7
  rw [q1 x y, q2 x y, q1 y x, q2 y x] at hxy
  rw [q1 x z, q2 x z, q1 z x, q2 z x] at hxz
  rw [q1 y z, q2 y z, q1 z y, q2 z y] at hyz
  linear_combination (h7 - hxy - hxz - hyz + h1 + h2 + h3) / 6

end Ward

end CoreLean
