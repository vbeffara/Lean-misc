import Mathlib

open Prod Function MeasureTheory Measure

class ProbSpace (Ω : Type*) extends MeasureSpace Ω where
  prob : IsProbabilityMeasure (volume : Measure Ω)

instance {Ω : Type*} [ProbSpace Ω] : IsProbabilityMeasure (volume : Measure Ω) := ProbSpace.prob

variable {Ω Ω' E F : Type*} [ProbSpace Ω] [ProbSpace Ω'] [MeasurableSpace E] [MeasurableSpace F]

def can_probSpace (_ : Measure E) := E
instance {μ : Measure E} : MeasurableSpace (can_probSpace μ) := by assumption
instance {μ : Measure E} : MeasureSpace (can_probSpace μ) := ⟨μ⟩
instance {μ : Measure E} [IsProbabilityMeasure μ] : ProbSpace (can_probSpace μ) := ⟨inferInstance⟩

noncomputable instance : ProbSpace (Ω × Ω') := ⟨inferInstance⟩

structure pmp (α β : Type*) [ProbSpace α] [ProbSpace β] :=
  (toFun : α → β)
  (meas : Measurable toFun)
  (map : .map toFun volume = volume)

namespace pmp

instance : CoeFun (pmp Ω Ω') (fun _ => Ω → Ω') := ⟨pmp.toFun⟩

def id : pmp Ω Ω := ⟨_root_.id, measurable_id, map_id⟩

def fst : pmp (Ω × Ω') Ω := ⟨Prod.fst, measurable_fst, by simp [volume]⟩

end pmp

class compatible (α₁ α₂ : Type*) [ProbSpace α₁] [ProbSpace α₂] :=
  (α : Type*)
  (hα : ProbSpace α)
  (p₁ : pmp α α₁)
  (p₂ : pmp α α₂)

namespace compatible

instance [I : compatible Ω Ω'] : ProbSpace I.α := I.hα

instance : compatible Ω Ω := ⟨Ω, inferInstance, pmp.id, pmp.id⟩
noncomputable instance : compatible Ω (Ω × Ω') := ⟨Ω × Ω', inferInstance, .fst, .id⟩
noncomputable instance : compatible (Ω × Ω') Ω := ⟨Ω × Ω', inferInstance, .id, .fst⟩

@[fun_prop] lemma meas_p₁ [I : compatible Ω Ω'] : Measurable I.p₁ := I.p₁.meas
@[fun_prop] lemma meas_p₂ [I : compatible Ω Ω'] : Measurable I.p₂ := I.p₂.meas

end compatible

@[ext] structure RV (Ω : Type*) [ProbSpace Ω] (E : Type*) [MeasurableSpace E] :=
  (toFun : Ω → E)
  (meas : Measurable toFun)

namespace RV

instance : CoeFun (RV Ω E) (fun _ => Ω → E) := ⟨RV.toFun⟩

@[fun_prop] instance {X : RV Ω E} : Measurable X.toFun := X.meas

instance [T : compatible Ω Ω'] : Coe (RV Ω E) (RV T.α E) := ⟨fun X => ⟨X ∘ T.p₁, by fun_prop⟩⟩
instance [T : compatible Ω Ω'] : Coe (RV Ω' E) (RV T.α E) := ⟨fun X => ⟨X ∘ T.p₂, by fun_prop⟩⟩

def map (X : RV Ω E) (f : E → F) (hf : Measurable f) : RV Ω F :=
  ⟨fun ω => f (X ω), by fun_prop⟩

def pair [T : compatible Ω Ω'] (X : RV Ω E) (Y : RV Ω' F) : RV T.α (E × F) :=
  ⟨fun ω => (X (T.p₁ ω), Y (T.p₂ ω)), by fun_prop⟩

instance [Add E] [MeasurableAdd₂ E] : Add (RV Ω E) :=
  ⟨fun X Y => ⟨fun ω => X ω + Y ω, by fun_prop⟩⟩

instance [T : compatible Ω Ω'] [Add E] [MeasurableAdd₂ E] : HAdd (RV Ω E) (RV Ω' E) (RV T.α E) :=
  ⟨fun X Y => X + Y⟩

-- "Let `Y` be an independent copy of `X`"
def copy (X : RV Ω E) : RV (Ω × Ω) E := ⟨X ∘ snd, by fun_prop⟩

def can (μ : Measure E) [IsProbabilityMeasure μ] : RV (can_probSpace μ) E := ⟨id, measurable_id⟩

noncomputable def law (X : RV Ω E) : Measure E := .map X volume

instance {X : RV Ω E} : IsProbabilityMeasure (law X) :=
  isProbabilityMeasure_map (by fun_prop)

end RV

@[ext] structure RV' (E : Type*) [MeasurableSpace E] :=
  (carrier : Type*)
  (hcarrier : ProbSpace carrier)
  (toRV : RV carrier E)

namespace RV'

instance {X : RV' E} : ProbSpace X.carrier := X.hcarrier

instance : CoeFun (RV' E) (fun X => X.carrier → E) := ⟨fun X => X.toRV⟩

instance : CoeOut (RV Ω E) (RV' E) := ⟨fun X => ⟨_, _, X⟩⟩

noncomputable def copy (X : RV' E) : RV' E := X.toRV.copy

end RV'

example (μ : Measure E) [IsProbabilityMeasure μ] : (RV.can μ).law = μ := by
  simp [RV.law, RV.can] ; rfl

example (X : RV Ω E) : (RV.pair X X.copy).law = X.law.prod X.law := by
  symm ; apply map_prod_map <;> fun_prop

example (X : RV Ω ℝ) : X + X.copy = X.copy + X := by ext ω ; apply add_comm
