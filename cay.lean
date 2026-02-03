import Cay.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.combinatorics.quiver.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs

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

theorem Isconnected {S : Set G} (prop : IsCayleyProperty S) :
    ∀ g h : CayleyGraph G S, Nonempty (path (CayleyGraph G S) g h) := by
  intro g h
  have : h.elt * g.elt⁻¹ ∈ Subgroup.closure S := by
    rw [prop.connected]
    exact Subgroup.mem_top _
  obtain ⟨list, hl, prod_eq⟩ := Subgroup.mem_closure_iff_exists_list.mp this
  let edges := list.map (fun s => ⟨s, ⟨hl s.2, by simp [mul_assoc]⟩⟩ : g ⟶ CayleyGraph.mk (g.elt * s))
  let path := Path.ofEdges edges
  use path
  induction list with
  | nil =>
    simp [Path.ofEdges, Path.refl]
  | cons a l ih =>
    simp [Path.ofEdges, Path.append, ih]
    have : ∀ s ∈ l, ∃ (e : CayleyGraph.mk (g.elt * a) ⟶ CayleyGraph.mk (g.elt * a * s)),
        e.val ∈ S ∧ (g.elt * a) * e.val = g.elt * a * s := by
      intro s hs
      use ⟨s, ⟨hl s hs, by simp [mul_assoc]⟩⟩
    exact this
