import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Int

universe u v
structure QuasiIsometricEmbedding
  (α : Type u)
  (β : Type v)
  [MetricSpace α]
  [MetricSpace β] where
  f : α → β
  K : ℝ
  C : ℝ
  req_1 : K ≥ 1
  req_2 : C ≥ 0
  main_req : ∀ x y : α, (1 / K) * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ K * dist x y + C


structure QuasiIsometry
  (α : Type u)
  (β : Type v)
  [MetricSpace α]
  [MetricSpace β]
  extends QuasiIsometricEmbedding α β where
  D : ℝ
  req_3 : D > 0
  main_req_2 : ∀ y : β, ∃ x : α, dist (f x) y ≤ D


structure GeodesicMetricSpace

noncomputable def seven_five_one : QuasiIsometry ℝ ℤ where
f := Int.floor
K := 1
C := 1
D := 1
req_1 := by norm_num
req_2 := by norm_num
req_3 := by norm_num
main_req := by
  intro x y
  sorry
