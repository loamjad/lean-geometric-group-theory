import Mathlib
variable {G : Type*} [Group G] (S : Set G)


structure IsCayleyProperty : Prop where
  loopless : 1 ∉ S
  symmetric : ∀ s ∈ S, s⁻¹ ∈ S
  connected : Subgroup.closure S = ⊤
structure CayleyGraph (G : Type*) (S : Set G) where
  elt : G

instance [Group G] (S : Set G) : Quiver (CayleyGraph G S) where
  Hom g h := {s // s ∈ S ∧ g.elt * s = h.elt}


def reverseEdge {S : Set G} (prop : IsCayleyProperty S)
    {g h : CayleyGraph G S} (e : g ⟶ h) : h ⟶ g :=
  ⟨e.val⁻¹,
    ⟨prop.symmetric e.val e.property.1, by
      have h_edge := e.property.2
      simp [← h_edge, mul_assoc]⟩⟩


open Quiver
namespace CayleyGraph
open Quiver


example (s : G) (s_mem : s ∈ S) : (⟨1⟩ : CayleyGraph G S) ⟶ (⟨s⟩ : CayleyGraph G S) :=
by
  use s
  constructor
  · exact s_mem
  · group




def shiftPath {G : Type*} [Group G] {S : Set G} (g : G) {u v : G}
    (p : Path (V := CayleyGraph G S) ⟨u⟩ ⟨v⟩) :
    Path (V := CayleyGraph G S) ⟨g * u⟩ ⟨g * v⟩ :=
  p.rec (motive := fun {b : CayleyGraph G S} _ => Path (V := CayleyGraph G S) ⟨g * u⟩ ⟨g * b.elt⟩)
    (Path.nil)
    (fun {b c : CayleyGraph G S} _ (e : b ⟶ c) ih =>
      let s := e.val
      let hs := e.property.1
      let h_eq := e.property.2
      let b_shifted : CayleyGraph G S := ⟨g * b.elt⟩
      let c_shifted : CayleyGraph G S := ⟨g * c.elt⟩
      let e_shifted : b_shifted ⟶ c_shifted :=
        ⟨s, ⟨hs, by
          simp only [b_shifted, c_shifted]
          rw [mul_assoc]
          rw [h_eq] ⟩⟩
      ih.cons e_shifted)





theorem Isconnected {G : Type*} [Group G] {S : Set G} (prop : IsCayleyProperty S) :
    ∀ (g h : CayleyGraph G S), Nonempty (Quiver.Path g h) := by
  intro g h
  let P (x : G) : Prop := Nonempty (Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨x⟩)
  have h_union : S ∪ S⁻¹ = S := by
    ext s; constructor
    · intro hx; cases hx with
      | inl h => exact h
      | inr h =>
        simp only [Set.mem_inv] at h
        let hs := prop.symmetric s⁻¹ h
        rw [inv_inv] at hs; exact hs
    · intro h; left; exact h
  have h_path : ∀ {x : G}, x ∈ Submonoid.closure S → P x := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | one => exact ⟨Path.nil⟩
    | mem s hs =>
      let e : (⟨1⟩ : CayleyGraph G S) ⟶ ⟨s⟩ := ⟨s, ⟨hs, by simp⟩⟩
      exact ⟨Path.nil.cons e⟩
    | mul a b ha hb iha ihb =>
      let ⟨pa⟩ := iha
      let ⟨pb⟩ := ihb
      let pb_s := shiftPath a pb
      have pb_shifted : Quiver.Path (V := CayleyGraph G S) (⟨a⟩ : CayleyGraph G S) ⟨a * b⟩ := by
        rw [mul_one] at pb_s
        exact pb_s
      exact ⟨pa.comp pb_shifted⟩
  have h_rel_subgroup : g.elt⁻¹ * h.elt ∈ Subgroup.closure S := by
    rw [prop.connected]; trivial
  have h_rel_monoid : g.elt⁻¹ * h.elt ∈ Submonoid.closure S := by
    let h_eq := Subgroup.closure_toSubmonoid S
    have h_eq_final : (Subgroup.closure S).toSubmonoid = Submonoid.closure S := by
      rw [h_union] at h_eq
      exact h_eq
    show g.elt⁻¹ * h.elt ∈ Submonoid.closure S
    rw [← h_eq_final]
    exact h_rel_subgroup
  obtain ⟨p_unit⟩ := h_path h_rel_monoid
  let p_final_raw := shiftPath g.elt p_unit
  have p_final : Quiver.Path g h := by
    try rw [mul_one] at p_final_raw
    rw [← mul_assoc] at p_final_raw
    rw [mul_inv_cancel g.elt] at p_final_raw
    rw [one_mul] at p_final_raw
    exact p_final_raw
  exact ⟨p_final⟩
end CayleyGraph
