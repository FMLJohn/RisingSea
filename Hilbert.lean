import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortExact.Preadditive
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.LinearAlgebra.Dimension
import Mathlib.LinearAlgebra.Finrank

structure additive {R : Type _} [CommRing R] (a : Π₀ (_ : ModuleCat R), ℤ) :
  Prop :=
sum_eq : ∀ (M₁ M₂ M₃ : ModuleCat R) (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
  (_ : CategoryTheory.ShortExact f g), (a M₁) + (a M₃) = a M₂