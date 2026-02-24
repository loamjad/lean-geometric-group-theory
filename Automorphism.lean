import Mathlib
import Cay
set_option linter.style.longLine false



/-- Theorem A: Left multiplication in a group induces an automorphism of the Cayley graph. -/
theorem cayley_left_mul_automorphism {G : Type*} [Group G] {S : Set G} (g : G) :
  -- 1. It is a bijection on vertices (an Equiv).
    Function.Bijective (fun (v : CayleyGraph G S) => (⟨g * v.elt⟩ : CayleyGraph G S)) ∧
  -- 2. It preserves edges bijectively: u ⟶ v exists iff g*u ⟶ g*v exists.
    ∀ (u v : CayleyGraph G S), Nonempty (u ⟶ v) ↔ Nonempty ((⟨g * u.elt⟩ : CayleyGraph G S) ⟶ (⟨g * v.elt⟩ : CayleyGraph G S)) := by
  constructor
  · --
    apply Function.bijective_iff_has_inverse.mpr
    use (fun v => ⟨g⁻¹ * v.elt⟩)
    constructor
    · intro v; simp [← mul_assoc]
    · intro v; simp [← mul_assoc]
  · --
    intro u v
    constructor
    · --
      rintro ⟨e⟩
      let e_shifted : (⟨g * u.elt⟩ : CayleyGraph G S) ⟶ ⟨g * v.elt⟩ :=
        ⟨e.val, ⟨e.property.1, by rw [mul_assoc, e.property.2]⟩⟩
      exact ⟨e_shifted⟩
    · --
      rintro ⟨e_prime⟩
      let e_back : u ⟶ v :=
        ⟨e_prime.val, ⟨e_prime.property.1, by
          have h := e_prime.property.2
          simp only [mul_assoc] at h
          exact mul_left_cancel h ⟩⟩
      exact ⟨e_back⟩



-- 1. Define label-preserving automorphisms.
structure LabeledAut (G : Type*) [Group G] (S : Set G) extends Equiv G G where
  map_rel : ∀ {u v : G} (s : S), u * s.val = v ↔ (toFun u) * s.val = (toFun v)
