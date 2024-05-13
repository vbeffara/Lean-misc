import Mathlib.Tactic

open Prod Function MeasureTheory

class ProbSpace (Ω : Type*) extends MeasureSpace Ω where
  prob : IsProbabilityMeasure (volume : Measure Ω)

instance {Ω : Type*} [ProbSpace Ω] : IsProbabilityMeasure (volume : Measure Ω) := ProbSpace.prob

variable {Ω Ω' E α α₁ α₂ : Type*} [ProbSpace Ω] [ProbSpace Ω'] [MeasurableSpace E]

noncomputable instance : ProbSpace (Ω × Ω') where prob := inferInstance

structure pmp (α β : Type*) [ProbSpace α] [ProbSpace β] :=
  (toFun : α → β)
  (meas : Measurable toFun)
  (map : Measure.map toFun volume = volume)

instance : CoeFun (pmp Ω Ω') (fun _ => Ω → Ω') := ⟨pmp.toFun⟩

namespace pmp

def id : pmp Ω Ω := ⟨_root_.id, measurable_id, Measure.map_id⟩

def fst : pmp (Ω × Ω') Ω := ⟨Prod.fst, measurable_fst,
  by { simpa only [measure_univ, one_smul] using @Measure.map_fst_prod Ω Ω' _ _ _ volume _ }⟩

end pmp

class compatible (α₁ α₂ : Type*) [ProbSpace α₁] [ProbSpace α₂] :=
  (α : Type*)
  (hα : ProbSpace α)
  (p₁ : pmp α α₁)
  (p₂ : pmp α α₂)

instance [I : compatible Ω Ω'] : ProbSpace I.α := I.hα

instance : compatible Ω Ω := ⟨Ω, inferInstance, pmp.id, pmp.id⟩
noncomputable instance : compatible Ω (Ω × Ω') := ⟨Ω × Ω', inferInstance, pmp.fst, pmp.id⟩
noncomputable instance : compatible (Ω × Ω') Ω := ⟨Ω × Ω', inferInstance, pmp.id, pmp.fst⟩

@[ext] structure RV (Ω : Type*) [ProbSpace Ω] (E : Type*) [MeasurableSpace E] :=
  (toFun : Ω → E)
  (meas : Measurable toFun)

instance : CoeFun (RV Ω E) (fun _ => Ω → E) := ⟨RV.toFun⟩

instance {X : RV Ω E} : Measurable X.toFun := X.meas

-- "Let `Y` be an independent copy of `X`"
def RV.copy (X : RV Ω E) : RV (Ω × Ω) E := ⟨X ∘ snd, X.meas.comp measurable_snd⟩

instance [T : compatible Ω Ω'] : Coe (RV Ω E) (RV T.α E) := ⟨fun X => ⟨X ∘ T.p₁, X.meas.comp T.p₁.meas⟩⟩
instance [T : compatible Ω Ω'] : Coe (RV Ω' E) (RV T.α E) := ⟨fun X => ⟨X ∘ T.p₂, X.meas.comp T.p₂.meas⟩⟩

instance [Add E] [MeasurableAdd₂ E] : Add (RV Ω E) :=
  ⟨fun X Y => ⟨fun ω => X ω + Y ω, X.meas.add Y.meas⟩⟩

instance [T : compatible Ω Ω'] [Add E] [MeasurableAdd₂ E] : HAdd (RV Ω E) (RV Ω' E) (RV T.α E) := by
  refine ⟨fun X Y => ⟨fun ω => X (T.p₁ ω) + Y (T.p₂ ω),
    Measurable.add (X.meas.comp T.p₁.meas) (Y.meas.comp T.p₂.meas)⟩⟩

@[ext] structure RV' (E : Type*) [MeasurableSpace E] :=
  (carrier : Type*)
  (hcarrier : ProbSpace carrier)
  (toRV : RV carrier E)

instance {X : RV' E} : ProbSpace X.carrier := X.hcarrier

instance : CoeFun (RV' E) (fun X => X.carrier → E) := ⟨fun X => X.toRV⟩

instance : CoeOut (RV Ω E) (RV' E) := ⟨fun X => ⟨_, _, X⟩⟩

noncomputable def RV'.copy (X : RV' E) : RV' E := X.toRV.copy

-- A few tests

noncomputable def double₁ (X : RV Ω ℝ) := X + X.copy
noncomputable def double₂ (X : RV Ω ℝ) := X.copy + X

example (X : RV Ω ℝ) : double₁ X = double₂ X := by ext ω ; apply add_comm
