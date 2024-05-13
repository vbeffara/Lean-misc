import Mathlib

open Topology Filter Uniformity Uniform MeasureTheory Set

variable {α β ι : Type*} [MeasurableSpace α] [TopologicalSpace α] [UniformSpace β]

lemma tendstoUniformly_iff_nhds (p : Filter ι) (F : ι → α → β) (b : β) :
    TendstoUniformly F (fun _ => b) p ↔ ∀ s ∈ 𝓝 b, ∀ᶠ i in p, ∀ a, F i a ∈ s := by
  refine ⟨fun h s hs => ?_, fun h u hu => h _ (UniformSpace.ball_mem_nhds _ hu)⟩
  obtain ⟨v, h1, h2⟩ := UniformSpace.mem_nhds_iff.mp hs
  filter_upwards [h v h1] with i h x using h2 (h x)

lemma tendstoUniformlyOnFilter_iff_nhds (p : Filter ι) (q : Filter α) (b : β) :
    TendstoUniformlyOnFilter F (fun _ => b) p q ↔ ∀ s ∈ 𝓝 b, ∀ᶠ n in p ×ˢ q, F n.1 n.2 ∈ s := by
  refine ⟨fun h s hs => ?_, fun h u hu => h _ (UniformSpace.ball_mem_nhds b hu)⟩
  obtain ⟨v, hv, h2⟩ := UniformSpace.mem_nhds_iff.mp hs
  filter_upwards [h v hv] with n hn using h2 hn

noncomputable instance toto : UniformSpace ENNReal :=
  (UniformSpace.comap ENNReal.orderIsoUnitIntervalBirational inferInstance).replaceTopology
    (StrictMono.induced_topology_eq_preorder (OrderIso.strictMono _)
      (by simp [RelIso.range_eq, ordConnected_univ])).symm

example : toto.toTopologicalSpace = ENNReal.instTopologicalSpace := rfl

def IsTight (μ : Measure α) : Prop := Tendsto μ (cocompact α).smallSets (𝓝 0)

example (μ : Measure α) :
    IsTight μ ↔ ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) ≤ ε := by
  simp only [IsTight, ne_eq, ENNReal.zero_ne_top, not_false_eq_true, ENNReal.tendsto_nhds,
    gt_iff_lt, ge_iff_le, zero_le, tsub_eq_zero_of_le, zero_add, mem_Icc, true_and,
    eventually_smallSets, mem_cocompact]
  apply forall₂_congr ; rintro ε - ; constructor
  · rintro ⟨A, ⟨K, h1, h2⟩, hA⟩ ; exact ⟨K, h1, hA Kᶜ h2⟩
  · rintro ⟨K, h1, h2⟩ ; exact ⟨Kᶜ, ⟨K, h1, by rfl⟩, fun A hA => μ.mono hA |>.trans h2⟩

def IsUniformlyTight (μ : ι → Measure α) : Prop :=
    TendstoUniformly (fun A i => μ i A) 0 (cocompact α).smallSets

example (μ : ι → Measure α) :
    IsUniformlyTight μ ↔ ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ ∀ i, μ i Kᶜ ≤ ε := by
  simp only [IsUniformlyTight, OfNat.ofNat, Pi.mulZeroClass, Pi.instZero, tendstoUniformly_iff_nhds,
    eventually_smallSets, mem_cocompact, gt_iff_lt]
  constructor
  · intro h ε hε
    obtain ⟨s, ⟨K, h1, h2⟩, h3⟩ := h _ (Iic_mem_nhds hε)
    exact ⟨K, h1, fun i => h3 _ h2 i⟩
  · intro h s hs
    obtain ⟨ε, hε, h1⟩ := ENNReal.nhds_zero_basis_Iic.mem_iff.mp hs
    obtain ⟨K, h2, h3⟩ := h ε hε
    exact ⟨Kᶜ, ⟨K, h2, by rfl⟩, fun t ht i => h1 ((μ i).mono ht |>.trans (h3 i))⟩

def IsTightAtFilter (μ : ι → Measure α) (F : Filter ι) : Prop :=
    TendstoUniformlyOnFilter (fun A i => μ i A) 0 (cocompact α).smallSets F

example (μ : ι → Measure α) (F : Filter ι) :
    IsTightAtFilter μ F ↔ ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ ∀ᶠ i in F, (μ i) Kᶜ ≤ ε := by
  rw [IsTightAtFilter]
  change TendstoUniformlyOnFilter _ (fun _ => 0) _ _ ↔ _
  rw [tendstoUniformlyOnFilter_iff_nhds]
  sorry

variable {μ : Measure α}

lemma add [TopologicalSpace α] {μ ν : Measure α} (hμ : IsTight μ) (hν : IsTight ν) :
    IsTight (μ + ν) := by
  simpa only [add_zero] using hμ.add hν
