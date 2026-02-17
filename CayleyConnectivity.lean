import Cay.Basic
import Mathlib

/-!
# Cayley Graph Connectivity

This file formalizes the connectivity theorem for Cayley graphs.

## Main Definitions

* `CayleyGraph G S`: A quiver representing the Cayley graph of group G with generating set S
* `IsCayleyProperty S`: Properties required for S to be a proper generating set
  - `loopless`: 1 ∉ S (no loops at vertices)
  - `symmetric`: s ∈ S → s⁻¹ ∈ S (undirected edges)
  - `connected`: Subgroup.closure S = ⊤ (S generates the whole group)

## Main Results

* `CayleyGraph.Isconnected`: Every Cayley graph with proper generating set is connected

## Implementation Strategy

The proof strategy follows these key steps:
1. **Reduction to paths from identity**: Show g ⟶ h connectivity by proving 1 ⟶ g⁻¹h connectivity
2. **Subgroup to submonoid conversion**: Use the fact that for symmetric S,
   Subgroup.closure S = Submonoid.closure S as topological spaces
3. **Submonoid induction**: Prove paths exist for all elements in Submonoid.closure S using:
   - Base case: trivial path 1 ⟶ 1
   - Generator case: single edge 1 ⟶ s for s ∈ S
   - Multiplication case: concatenate shifted paths using left translation invariance
4. **Path shifting**: Implement left multiplication on paths to handle composition

## Mathematical Background

A Cayley graph Cay(G, S) has:
- Vertices: elements of G
- Edges: g ⟶ gs for each g ∈ G, s ∈ S

The graph is connected iff S generates G (i.e., ⟨S⟩ = G).
-/

variable {G : Type*} [Group G] (S : Set G)

/-- Properties required for S to be a proper Cayley graph generating set -/
structure IsCayleyProperty : Prop where
  loopless : 1 ∉ S                              -- No self-loops (edges from vertex to itself)
  symmetric : ∀ s ∈ S, s⁻¹ ∈ S                 -- Undirected edges (s ∈ S ↔ s⁻¹ ∈ S)
  connected : Subgroup.closure S = ⊤           -- S generates the entire group G

/-- A Cayley graph as a quiver structure -/
structure CayleyGraph (G : Type*) (S : Set G) where
  elt : G                                       -- Each vertex corresponds to a group element

/-- Quiver instance: edges from g to h labeled by generators s where g*s = h -/
instance [Group G] (S : Set G) : Quiver (CayleyGraph G S) where
  Hom g h := {s // s ∈ S ∧ g.elt * s = h.elt}  -- Edge exists iff ∃s∈S such that g*s = h

/-- Every edge has a reverse edge (due to symmetry of generating set) -/
def reverseEdge {S : Set G} (prop : IsCayleyProperty S)
    {g h : CayleyGraph G S} (e : g ⟶ h) : h ⟶ g :=
  ⟨e.val⁻¹,                                     -- Reverse edge labeled by s⁻¹
    ⟨prop.symmetric e.val e.property.1,         -- s⁻¹ ∈ S since S is symmetric
     by have h_edge := e.property.2             -- If g*s = h, then h*s⁻¹ = g
        simp [← h_edge, mul_assoc]⟩⟩

open Quiver
namespace CayleyGraph
open Quiver

/-- Example: constructing an edge from identity to generator -/
example (s : G) (s_mem : s ∈ S) : (⟨1⟩ : CayleyGraph G S) ⟶ (⟨s⟩ : CayleyGraph G S) :=
by
  -- Goal: construct element of subtype {s // s ∈ S ∧ 1 * s = s}
  use s                                         -- Use generator s as edge label
  constructor                                   -- Split into membership and equation
  · exact s_mem                                -- s ∈ S by assumption
  · group                                      -- 1 * s = s by group axioms

/-- Left multiplication on paths: if p : u ⟶ v, then g*p : g*u ⟶ g*v
    This implements the left translation invariance of Cayley graphs -/
def shiftPath {G : Type*} [Group G] {S : Set G} (g : G) {u v : G}
    (p : Path (V := CayleyGraph G S) ⟨u⟩ ⟨v⟩) :
    Path (V := CayleyGraph G S) ⟨g * u⟩ ⟨g * v⟩ :=
  p.rec
    -- Motive: for any intermediate vertex b, construct path ⟨g*u⟩ ⟶ ⟨g*b.elt⟩
    (motive := fun {b : CayleyGraph G S} _ => Path (V := CayleyGraph G S) ⟨g * u⟩ ⟨g * b.elt⟩)
    -- Base case: empty path becomes empty path
    (Path.nil)
    -- Inductive case: cons edge to existing path
    (fun {b c : CayleyGraph G S} _ (e : b ⟶ c) ih =>
      -- Extract edge information
      let s := e.val                            -- Edge label (generator)
      let hs := e.property.1                   -- s ∈ S
      let h_eq := e.property.2                 -- b.elt * s = c.elt

      -- Construct shifted vertices
      let b_shifted : CayleyGraph G S := ⟨g * b.elt⟩
      let c_shifted : CayleyGraph G S := ⟨g * c.elt⟩

      -- Construct shifted edge: if b --s--> c then (g*b) --s--> (g*c)
      let e_shifted : b_shifted ⟶ c_shifted :=
        ⟨s, ⟨hs, by
          -- Need to prove: (g * b.elt) * s = g * c.elt
          simp only [b_shifted, c_shifted]     -- Unfold vertex definitions
          rw [mul_assoc]                       -- (g * b.elt) * s = g * (b.elt * s)
          rw [h_eq]                           -- g * (b.elt * s) = g * c.elt using b*s=c
        ⟩⟩

      ih.cons e_shifted)                       -- Prepend shifted edge to inductive path

/--
MAIN THEOREM: Cayley Graph Connectivity

Every Cayley graph with a proper generating set is connected.
Specifically, for any two vertices g, h, there exists a path g ⟶ h.

PROOF STRATEGY:
1. Reduce g ⟶ h connectivity to 1 ⟶ (g⁻¹h) connectivity via path shifting
2. Convert subgroup closure to submonoid closure using symmetry of S
3. Use submonoid induction to show all elements in closure(S) are reachable from 1
4. Apply path shifting to get general connectivity result

KEY INSIGHT: The symmetry condition S = S⁻¹ allows us to treat the subgroup closure
as a submonoid closure, enabling simpler induction without inverse cases.
-/
theorem Isconnected {G : Type*} [Group G] {S : Set G} (prop : IsCayleyProperty S) :
    ∀ (g h : CayleyGraph G S), Nonempty (Quiver.Path g h) := by
  intro g h

  -- STEP 1: Define the key predicate - reachability from identity
  -- P(x) := "there exists a path from vertex 1 to vertex x"
  let P (x : G) : Prop := Nonempty (Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨x⟩)

  -- STEP 2: Prove S ∪ S⁻¹ = S using symmetry
  -- This is crucial for converting subgroup to submonoid closure
  have h_union : S ∪ S⁻¹ = S := by
    ext s                                       -- Prove set equality element by element
    constructor
    · intro hx                                  -- Case: s ∈ S ∪ S⁻¹
      cases hx with
      | inl h => exact h                       -- If s ∈ S, done
      | inr h =>                               -- If s ∈ S⁻¹
        simp only [Set.mem_inv] at h          -- Then s⁻¹⁻¹ ∈ S, i.e., s ∈ S
        let hs := prop.symmetric s⁻¹ h
        rw [inv_inv] at hs
        exact hs
    · intro h; left; exact h                   -- If s ∈ S then s ∈ S ∪ S⁻¹

  -- STEP 3: Main induction - prove P(x) for all x in Submonoid.closure S
  -- This avoids dealing with inverse elements directly
  have h_path : ∀ {x : G}, x ∈ Submonoid.closure S → P x := by
    intro x hx
    -- Use submonoid induction with three cases: one, mem, mul
    induction hx using Submonoid.closure_induction with

    | one =>
      -- BASE CASE: P(1) - trivial empty path from 1 to 1
      exact ⟨Path.nil⟩

    | mem s hs =>
      -- GENERATOR CASE: P(s) for s ∈ S - single edge path 1 --s--> s
      let e : (⟨1⟩ : CayleyGraph G S) ⟶ ⟨s⟩ := ⟨s, ⟨hs, by simp⟩⟩
      exact ⟨Path.nil.cons e⟩

    | mul a b ha hb iha ihb =>
      -- MULTIPLICATION CASE: P(a*b) given P(a) and P(b)
      -- Strategy: concatenate path 1⟶a with shifted path a⟶a*b
      let ⟨pa⟩ := iha                         -- Path 1 ⟶ a
      let ⟨pb⟩ := ihb                         -- Path 1 ⟶ b

      -- Shift pb by left multiplication: 1⟶b becomes a⟶a*b
      let pb_s := shiftPath a pb

      -- Type correction: a * 1 = a
      have pb_shifted : Quiver.Path (V := CayleyGraph G S) (⟨a⟩ : CayleyGraph G S) ⟨a * b⟩ := by
        rw [mul_one] at pb_s
        exact pb_s

      -- Concatenate: 1⟶a followed by a⟶a*b gives 1⟶a*b
      exact ⟨pa.comp pb_shifted⟩

  -- STEP 4: Convert the target g ⟶ h into reachability from identity
  -- Key insight: g ⟶ h is equivalent to 1 ⟶ g⁻¹h via path shifting

  -- First show g⁻¹h is in the subgroup closure
  have h_rel_subgroup : g.elt⁻¹ * h.elt ∈ Subgroup.closure S := by
    rw [prop.connected]                        -- Subgroup.closure S = ⊤
    trivial                                    -- Everything is in ⊤

  -- Convert subgroup membership to submonoid membership
  have h_rel_monoid : g.elt⁻¹ * h.elt ∈ Submonoid.closure S := by
    -- Use the fundamental lemma: (Subgroup.closure S).toSubmonoid = Submonoid.closure (S ∪ S⁻¹)
    let h_eq := Subgroup.closure_toSubmonoid S

    -- Simplify S ∪ S⁻¹ to S using symmetry
    have h_eq_final : (Subgroup.closure S).toSubmonoid = Submonoid.closure S := by
      rw [h_union] at h_eq
      exact h_eq

    -- Apply the conversion
    show g.elt⁻¹ * h.elt ∈ Submonoid.closure S
    rw [← h_eq_final]
    exact h_rel_subgroup                       -- This is definitionally equal

  -- STEP 5: Construct the final path using shifting
  -- Get path 1 ⟶ g⁻¹h, then shift by g to get g ⟶ h
  obtain ⟨p_unit⟩ := h_path h_rel_monoid      -- Path 1 ⟶ g⁻¹h

  let p_final_raw := shiftPath g.elt p_unit    -- Shift to get g ⟶ g*(g⁻¹h)

  -- Simplify the endpoint: g*(g⁻¹*h) = (g*g⁻¹)*h = 1*h = h
  have p_final : Quiver.Path g h := by
    try rw [mul_one] at p_final_raw            -- Clean up any 1's from shifting
    rw [← mul_assoc] at p_final_raw           -- g * (g⁻¹ * h) = (g * g⁻¹) * h
    rw [mul_inv_cancel g.elt] at p_final_raw  -- g * g⁻¹ = 1
    rw [one_mul] at p_final_raw               -- 1 * h = h
    exact p_final_raw

  exact ⟨p_final⟩                              -- Return the constructed path

end CayleyGraph
