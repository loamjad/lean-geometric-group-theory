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





--subgroup.closure_induction will help here. wildly
