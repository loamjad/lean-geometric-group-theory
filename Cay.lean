import Mathlib
set_option linter.style.longLine false
variable {G : Type*} [Group G] (S : Set G)




def IsSymmetric (S : Set G) : Prop := ∀ s ∈ S, s⁻¹ ∈ S
def IsGenerating (S : Set G) : Prop := Subgroup.closure S = ⊤
def IsLoopless (S : Set G) : Prop := 1 ∉ S


structure CayleyGraph (G : Type*) (S : Set G) where
  elt : G

instance [Group G] (S : Set G) : Quiver (CayleyGraph G S) where
  Hom g h := {s // s ∈ S ∧ g.elt * s = h.elt}


def reverseEdge {S : Set G} (prop : IsSymmetric S)
    {g h : CayleyGraph G S} (e : g ⟶ h) : h ⟶ g :=
  ⟨e.val⁻¹,
    ⟨prop e.val e.property.1, by
      have h_edge := e.property.2
      simp [← h_edge, mul_assoc]⟩⟩


open Quiver
namespace CayleyGraph


example (s : G) (s_mem : s ∈ S) : (⟨1⟩ : CayleyGraph G S) ⟶ (⟨s⟩ : CayleyGraph G S) :=
by
  -- The goal is a subtype object: {s // s ∈ S ∧ 1 * s = s}.
  -- We use angle brackets to construct this object.
  use s
  -- The goal is now split into two parts:
  -- 1. s ∈ S
  -- 2. 1 * s = s
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





/-- Connectivity proof for the Cayley graph. -/
theorem Isconnected {G : Type*} [Group G] {S : Set G} (prop1 : IsSymmetric S) (prop2 : IsGenerating S) :
    ∀ (g h : CayleyGraph G S), Nonempty (Quiver.Path g h) := by
  intro g h
  -- Define P x: there exists a path from the identity element 1 to x.
  let P (x : G) : Prop := Nonempty (Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨x⟩)
  -- 1. Show that symmetry of S lets us reduce the subgroup closure to a monoid closure.
  have h_union : S ∪ S⁻¹ = S := by
    ext s; constructor
    · intro hx; cases hx with
      | inl h => exact h
      | inr h =>
        simp only [Set.mem_inv] at h
        let hs := prop1 s⁻¹ h
        rw [inv_inv] at hs; exact hs
    · intro h; left; exact h
  -- 2. Core induction: every element in the monoid closure has a path from 1.
  have h_path : ∀ {x : G}, x ∈ Submonoid.closure S → P x := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | one => exact ⟨Path.nil⟩
    | mem s hs =>
      -- Construct the edge 1 -> s.
      let e : (⟨1⟩ : CayleyGraph G S) ⟶ ⟨s⟩ := ⟨s, ⟨hs, by simp⟩⟩
      exact ⟨Path.nil.cons e⟩
    | mul a b ha hb iha ihb =>
      let ⟨pa⟩ := iha
      let ⟨pb⟩ := ihb
      -- Shift pb (1 -> b) by left multiplication by a to get (a -> a*b).
      let pb_s := shiftPath a pb
      -- Fix the type using a * 1 = a.
      have pb_shifted : Quiver.Path (V := CayleyGraph G S) (⟨a⟩ : CayleyGraph G S) ⟨a * b⟩ := by
        rw [mul_one] at pb_s
        exact pb_s
      exact ⟨pa.comp pb_shifted⟩
  -- 3. Convert the target g -> h into a path starting from 1.
  -- Let p_unit be a path of type: 1 -> g⁻¹h.
  have h_rel_subgroup : g.elt⁻¹ * h.elt ∈ Subgroup.closure S := by
    rw [prop2]; trivial
  -- Convert subgroup membership to monoid membership.
  have h_rel_monoid : g.elt⁻¹ * h.elt ∈ Submonoid.closure S := by
    -- Use the base lemma: (closure S).toSubmonoid = Submonoid.closure (S ∪ S⁻¹).
    let h_eq := Subgroup.closure_toSubmonoid S
    -- Simplify S ∪ S⁻¹ to S inside h_eq.
    have h_eq_final : (Subgroup.closure S).toSubmonoid = Submonoid.closure S := by
      rw [h_union] at h_eq
      exact h_eq
    -- Key step: use `show` to state the goal explicitly, then rewrite by h_eq_final.
    change g.elt⁻¹ * h.elt ∈ Submonoid.closure S
    rw [← h_eq_final]
    -- The goal is now g.elt⁻¹ * h.elt ∈ (Subgroup.closure S).toSubmonoid,
    -- which is definitionally equivalent to h_rel_subgroup.
    exact h_rel_subgroup
  -- Obtain the path and shift it.
  obtain ⟨p_unit⟩ := h_path h_rel_monoid
  let p_final_raw := shiftPath g.elt p_unit
  have p_final : Quiver.Path g h := by
    -- Clear any remaining mul_one simplification first.
    try rw [mul_one] at p_final_raw
    -- g * (g⁻¹ * h) -> (g * g⁻¹) * h
    rw [← mul_assoc] at p_final_raw
    -- g * g⁻¹ -> 1 (via mul_inv_cancel)
    rw [mul_inv_cancel g.elt] at p_final_raw
    -- 1 * h -> h
    rw [one_mul] at p_final_raw
    exact p_final_raw
  exact ⟨p_final⟩







theorem generating_of_connected {G : Type*} [Group G] {S : Set G} :
    (∀ g h : CayleyGraph G S, Nonempty (Quiver.Path g h)) → Subgroup.closure S = ⊤ := by
  intro h_conn
  -- To prove subgroup closure is top, it suffices to show every g lies in the closure.
  ext g
  simp only [Subgroup.mem_top, iff_true]
  -- Use connectivity to get a path from 1 to g.
  obtain ⟨p⟩ := h_conn ⟨1⟩ ⟨g⟩
  let n := p.length
  have : ∀ {u v : CayleyGraph G S}, (p : Quiver.Path u v) → u.elt ∈ Subgroup.closure S → v.elt ∈ Subgroup.closure S := by
    intro u v path hu
    induction path generalizing hu with
    | nil => exact hu
    | cons tail e ih =>
      obtain ⟨s, hs, heq⟩ := e -- heq : tail_end.elt * s = v.elt
      rw [← heq]
      exact Subgroup.mul_mem _ (ih hu) (Subgroup.subset_closure hs)
  exact this p (Subgroup.one_mem _)


theorem connected_iff_generating {G : Type*} [Group G] {S : Set G} (h_symm : IsSymmetric S) :
    (∀ g h : CayleyGraph G S, Nonempty (Quiver.Path g h)) ↔ IsGenerating S := by
  constructor
  · -- forward direction: connectivity implies generating
    exact generating_of_connected
  · -- reverse direction: generating implies connectivity
    intro h_gen
    exact Isconnected h_symm h_gen

end CayleyGraph
