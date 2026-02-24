import Mathlib
import Cay
set_option linter.style.longLine false


/-- Define word length: the shortest path length from the identity element to g. -/
noncomputable def wordLength {G : Type*} [Group G] (S : Set G) (g : G) : ℕ :=
  let lengths := {n : ℕ | ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨g⟩, p.length = n}
  sInf lengths

/-- Define word distance via left-translation invariance. -/
noncomputable def wordDist {G : Type*} [Group G] (S : Set G) (g h : G) : ℕ :=
  wordLength S (g⁻¹ * h)
