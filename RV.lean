import Mathlib.Tactic

open Prod Function MeasureTheory

variable {Ω Ω' E α α₁ α₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]

structure pmp (α β : Type*) [MeasureSpace α] [MeasureSpace β] :=
  (toFun : α → β)
  (meas : Measurable toFun)
  (map : Measure.map toFun volume = volume)

class compatible (α₁ α₂ : Type*) [MeasurableSpace α₁] [MeasurableSpace α₂] :=
  (α : Type*) (hα : MeasurableSpace α)
  (p₁ : α → α₁) (h₁ : Measurable p₁)
  (p₂ : α → α₂) (h₂ : Measurable p₂)

instance [I : compatible Ω Ω'] : MeasurableSpace I.α := I.hα

instance : compatible Ω Ω := ⟨Ω, inferInstance, id, measurable_id, id, measurable_id⟩
instance : compatible Ω (Ω × Ω') := ⟨Ω × Ω', inferInstance, fst, measurable_fst, id, measurable_id⟩
instance : compatible (Ω × Ω') Ω := ⟨Ω × Ω', inferInstance, id, measurable_id, fst, measurable_fst⟩

@[ext] structure RV (Ω : Type*) [MeasurableSpace Ω] (E : Type*) [MeasurableSpace E] :=
  (toFun : Ω → E)
  (meas : Measurable toFun)

instance : CoeFun (RV Ω E) (fun _ => Ω → E) := ⟨RV.toFun⟩

instance {X : RV Ω E} : Measurable X.toFun := X.meas

-- "Let `Y` be an independent copy of `X`"
def RV.copy (X : RV Ω E) : RV (Ω × Ω) E := ⟨X ∘ snd, X.meas.comp measurable_snd⟩

instance [T : compatible Ω Ω'] : Coe (RV Ω E) (RV T.α E) := ⟨λ X => ⟨X ∘ T.p₁, X.meas.comp T.h₁⟩⟩
instance [T : compatible Ω Ω'] : Coe (RV Ω' E) (RV T.α E) := ⟨λ X => ⟨X ∘ T.p₂, X.meas.comp T.h₂⟩⟩

instance [Add E] [MeasurableAdd₂ E] : Add (RV Ω E) :=
  ⟨fun X Y => ⟨fun ω => X ω + Y ω, X.meas.add Y.meas⟩⟩

instance [T : compatible Ω Ω'] [Add E] [MeasurableAdd₂ E] : HAdd (RV Ω E) (RV Ω' E) (RV T.α E) := by
  refine ⟨fun X Y => ⟨fun ω => X (T.p₁ ω) + Y (T.p₂ ω),
    Measurable.add (X.meas.comp T.h₁) (Y.meas.comp T.h₂)⟩⟩

@[ext] structure RV' (E : Type*) [MeasurableSpace E] :=
  (carrier : Type*)
  (hcarrier : MeasurableSpace carrier)
  (toRV : RV carrier E)

instance {X : RV' E} : MeasurableSpace X.carrier := X.hcarrier

instance : CoeFun (RV' E) (fun X => X.carrier → E) := ⟨fun X => X.toRV⟩

instance : CoeOut (RV Ω E) (RV' E) := ⟨fun X => ⟨_, _, X⟩⟩

def RV'.copy (X : RV' E) : RV' E := X.toRV.copy

-- A few tests

def double₁ (X : RV Ω ℝ) := X + X.copy
def double₂ (X : RV Ω ℝ) := X.copy + X

example (X : RV Ω ℝ) : double₁ X = double₂ X := by ext ω ; apply add_comm
