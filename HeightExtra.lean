import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Module.LocalizedModule

/-
Codes written in the process of proving the theorem that the height of `I` is
equal to the Krull dimension of the localization of `R` at `I`, which were
later found to be unnecessary for the proof.
-/
section extraCodes

variable {R : Type _} [CommRing R] (J : Ideal R) (I : PrimeSpectrum R)

/--
For any ideal `J` and submonoid `x` of `R`, `Ideal.localization J x` is
the ideal `J.map (algebraMap R (Localization x))` of `Localization x`.
-/
abbrev _root_.Ideal.localization (x : Submonoid R) : Ideal (Localization x) :=
  J.map (algebraMap R (Localization x))

/--
For any ideals `J` and `I` of `R` such that `I` is prime, `Ideal.localizationAtPrime J I`
is defined as `J.localization I.asIdeal.primeCompl`.
-/
abbrev _root_.Ideal.localizationAtPrime := J.localization I.asIdeal.primeCompl

/-- The canonical map from the ideal J of R to its image JR_I in the localisation. -/
@[simps apply] def _root_.Ideal.toLocalization (x : Submonoid R) :
  J →ₗ[R] J.localization x where
  toFun := λ x ↦ ⟨Localization.mk x 1, Submodule.subset_span ⟨_, x.2, rfl⟩⟩
  map_add' := λ _ _ ↦ Subtype.ext (Localization.add_mk_self _ _ _).symm
  map_smul' := λ _ _ ↦ Subtype.ext (Localization.smul_mk _ _ _).symm

@[simps!] def _root_.Localization.divBy {x : Submonoid R} (s : x) :
  Module.End (Localization x) (Localization x) where
    toFun := λ x ↦ (Localization.mk 1 s) * x
    map_add' := mul_add _
    map_smul' := λ r x ↦ by dsimp; ring

lemma _root_.Localization.divBy_apply_mem {y : Submonoid R} (s : y)
  (x) (hx : x ∈ J.localization y) :
  Localization.divBy s x ∈ J.localization y := by
simpa only [Localization.divBy_apply] using
  (J.localization y).mul_mem_left
    (Submonoid.LocalizationMap.mk' (Localization.monoidOf y) 1 s) hx

variable {I}

def _root_.Localization.divBy' {y : Submonoid R} (s : y) :
  Module.End R (J.localization y) :=
(LinearMap.restrict _ $ Localization.divBy_apply_mem J s).restrictScalars R

lemma _root_.Localization.divBy'_right_inv {y : Submonoid R} (s : y) :
  algebraMap R _ s * Localization.divBy' J s = 1 :=
LinearMap.ext $ λ x ↦ show (s : R) • Localization.divBy' J s x = x from Subtype.ext $
  show (s : R) • (Localization.mk 1 s * x) = x by rw [←smul_mul_assoc, Localization.smul_mk,
    smul_eq_mul, mul_one, Localization.mk_self, one_mul]

lemma _root_.LocalizationAtPrime.divBy'_left_inv  {y : Submonoid R} (s : y) :
  (Localization.divBy' J s) * algebraMap R _ s = 1 :=
LinearMap.ext $ λ x ↦ Subtype.ext $ show Localization.mk 1 s * ((s : R) • x) = x
  by erw [mul_smul_comm, ←smul_mul_assoc, Localization.smul_mk, smul_eq_mul, mul_one,
    Localization.mk_self, one_mul]

lemma toIdealImageSpan_exist_eq  {z : Submonoid R} y :
  ∃ (x : J × z), (x.2 : R) • y = J.toLocalization z x.1 := by
{ rcases y with ⟨y, h⟩
  apply Submodule.span_induction' ?_ ?_ ?_ ?_ h
  · rintro _ ⟨_, h, rfl⟩
    refine ⟨⟨⟨_, h⟩, 1⟩, one_smul _ _⟩
  · refine ⟨⟨0, 1⟩, ?_⟩
    simp only [OneMemClass.coe_one, one_smul, map_zero, Submodule.mk_eq_zero]
  · rintro x hx y hy ⟨⟨mx, nx⟩, hmnx⟩ ⟨⟨my, ny⟩, hmny⟩
    refine ⟨⟨(nx : R) • my + (ny : R) • mx, nx * ny⟩, Subtype.ext ?_⟩
    have : ny.1 • nx.1 • x + nx.1 • ny.1 • y =
      ny.1 • Localization.mk mx.1 1 + nx • Localization.mk my.1 1
    · exact Subtype.ext_iff.mp (congr_arg₂ (. + .) (congr_arg ((. • .) (ny : R)) hmnx)
      (congr_arg ((. • .) (nx : R)) hmny))
    rw [smul_comm, ←smul_add, ←smul_add, Localization.smul_mk] at this
    erw [Localization.smul_mk] at this
    rw [Localization.add_mk_self, ←mul_smul, add_comm (_ • _)] at this
    exact this
  · rintro a x hx ⟨⟨c1, c2⟩, (hc : (c2 : R) • _ = _)⟩
    induction a using Localization.induction_on with | H a => ?_
    induction x using Localization.induction_on with | H x => ?_
    rcases a with ⟨d1, d2⟩
    rcases x with ⟨x1, x2⟩
    refine ⟨⟨⟨d1 • c1, J.mul_mem_left d1 (SetLike.coe_mem c1)⟩, d2 * c2⟩,
      Subtype.ext (?_ : (_ * _) • (Localization.mk _ _ * _) = Localization.mk (_ • _) _)⟩
    rw [←Localization.smul_mk (d1 : R) (c1 : R) 1, show Localization.mk c1.1 1 = c2.1 •
      Localization.mk _ _ from (Subtype.ext_iff.mp hc).symm, Localization.smul_mk,
      Localization.smul_mk, Localization.mk_mul, Localization.smul_mk, smul_eq_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by dsimp; ring⟩ }

lemma _root_.Ideal.toLocalization_apply_eq_iff (y : Submonoid R) (x₁ x₂) :
  J.toLocalization y x₁ = J.toLocalization y x₂ ↔
    ∃ (c : y), (c : R) • x₂ = (c : R) • x₁ :=
Subtype.ext_iff.trans $ Localization.mk_eq_mk_iff.trans $ Localization.r_iff_exists.trans $
  exists_congr $ λ x ↦ eq_comm.trans $ Iff.symm $ Subtype.ext_iff.trans $ by simp [smul_eq_mul]

instance (y : Submonoid R) : IsLocalizedModule y (J.toLocalization y) where
  map_units := λ s ↦ ⟨⟨_, _, Localization.divBy'_right_inv _ s,
    LocalizationAtPrime.divBy'_left_inv _ s⟩, rfl⟩
  surj' := toIdealImageSpan_exist_eq J
  eq_iff_exists' := J.toLocalization_apply_eq_iff _ _ _

noncomputable def _root_.Ideal.localizedModuleEquivLocalization (y : Submonoid R) :
  LocalizedModule y J ≃ₗ[R] J.localization y :=
IsLocalizedModule.iso _ $ J.toLocalization y

lemma _root_.Ideal.localizedModuleEquivLocalization_apply (y : Submonoid R) (a b) :
    J.localizedModuleEquivLocalization y (LocalizedModule.mk a b) =
    ⟨Localization.mk a b, by simpa only [show Localization.mk (a : R) b =
      (Localization.mk 1 b) * (Localization.mk ↑a 1) by rw [Localization.mk_mul, one_mul, mul_one]]
        using Ideal.mul_mem_left _ _ (Ideal.apply_coe_mem_map _ J a)⟩ :=
(Module.End_algebraMap_isUnit_inv_apply_eq_iff _ _ _).mpr <| by
  refine Subtype.ext (?_ : Localization.mk _ _ = _ • Localization.mk (a : R) b)
  rw [Localization.smul_mk, smul_eq_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

end extraCodes