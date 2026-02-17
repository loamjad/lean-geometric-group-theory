import Proj1.Basic
import Mathlib

variable (G : Type u) [Group G]
def Generates (S : Set G) : Prop :=
∀ g : G, g ∈ Subgroup.closure S


structure finGenSet (G : Type u) [Group G] where
    S : Set G
    gen : Generates (G := G) S
    inverses : ∀ {g}, g ∈ S → g⁻¹ ∈ S

variable (S : finGenSet (G := G))

def isCayleyEdge {G : Type u} [Group G] (S : finGenSet (G := G)) (a b : G) : Type u :=
{s : S.S // a * s.val = b}

structure CayleyGraph where
(G: Type u)
[group : Group G]
(S : finGenSet (G := G))

attribute [instance] CayleyGraph.group

instance (c : CayleyGraph) : Quiver c.G where
    Hom a b := isCayleyEdge (S := c.S) a b

theorem goesto_e (c : CayleyGraph) :
∀ {x : c.G}, x ∈ Subgroup.closure c.S.S → Nonempty (Quiver.Path x (1 : c.G) ) :=  --i dont like lean
sorry

variable {c : CayleyGraph}
def Reachable (a b : c.G) : Prop := Nonempty (Quiver.Path a b)

def Path.combine {q : Type u} [Quiver q] {u v w : q} : Quiver.Path u v → Quiver.Path v w → Quiver.Path u w
  | p, Quiver.Path.nil => p
  | p, Quiver.Path.cons β e => Quiver.Path.cons (Path.combine p β) e

def translateEdge (t : c.G) {a b : c.G} :
  isCayleyEdge c.S a b →
  isCayleyEdge c.S (t*a) (t*b)
  | e => ⟨e.1, by simp[mul_assoc, e.2]⟩

-- have to reverse, quiver is directed

def reverse_edge {a b : c.G} :
  isCayleyEdge c.S a b → isCayleyEdge c.S b a
| e =>
  have invPf : (e.1.val)⁻¹ ∈ c.S.S :=
    c.S.inverses e.1.property
  let generatingInverse : c.S.S :=
    ⟨(e.1.val)⁻¹, invPf⟩
  have invClosure : b * generatingInverse.val = a := by
    calc
    b * generatingInverse.val
    = (a * e.1.val) * (e.1.val)⁻¹ := by simpa [e.2, generatingInverse]
    _ = a := by simp [mul_assoc]
  ⟨generatingInverse, invClosure⟩

def reversePath {a b : c.G} : Quiver.Path a b → Quiver.Path b a
  | Quiver.Path.nil => Quiver.Path.nil
  | Quiver.Path.cons p e => Path.combine
        (Quiver.Path.cons Quiver.Path.nil (reverse_edge (c := c) e))
        (reversePath p)

def translatePath (t : c.G) {a b : c.G} : Quiver.Path a b → Quiver.Path (t * a) (t * b)
  | Quiver.Path.nil => Quiver.Path.nil
  | Quiver.Path.cons p e =>
      Quiver.Path.cons (translatePath t p) (translateEdge (c := c) t e)

--major thm

theorem one_is_reachable (x : c.G)
    (hypothesis : x ∈ Subgroup.closure c.S.S) :
    Reachable (c := c) (1 : c.G) x := by
  refine Subgroup.closure_induction
    (k := c.S.S)
    (p := fun g _ => Reachable (c := c) (1 : c.G) g)
    ?mem ?one ?mul ?inv hypothesis

  · intro s hs
    refine ⟨Quiver.Path.cons Quiver.Path.nil ?_⟩
    exact ⟨⟨s, hs⟩, by simp⟩

  · exact ⟨Quiver.Path.nil⟩

  · intro a b ha hb pa pb
    rcases pa with ⟨p1a⟩
    rcases pb with ⟨p1b⟩
    refine ⟨Path.combine p1a ?_⟩
    simpa [one_mul] using
      (translatePath (c := c) a (a := (1 : c.G)) (b := b) p1b)

  · intro a ha pa
    rcases pa with ⟨p1a⟩
    have pA1 : Quiver.Path a (1 : c.G) := reversePath (c := c) p1a
    have p11inv : Quiver.Path (a⁻¹ * a) (a⁻¹ * (1 : c.G)) :=
      translatePath (c := c) (a⁻¹) pA1
    exact ⟨by simpa [mul_assoc] using p11inv⟩
