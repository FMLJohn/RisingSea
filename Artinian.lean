import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Artinian

variable {R : Type _} [CommRing R] [IsArtinianRing R]
variable (p : Ideal R) [Ideal.IsPrime p]

instance Ideal.IsPrime.isMaximal_of_isArtinianRing : p.IsMaximal := by
{ refine' Ideal.Quotient.maximal_of_isField p {
    exists_pair_ne := ⟨0, 1, zero_ne_one⟩
    mul_comm := mul_comm
    mul_inv_cancel := by
      intro x hx
      haveI ins1 : IsArtinianRing (R ⧸ p) := (@Ideal.Quotient.mk_surjective R _ p).isArtinianRing
      obtain ⟨n, hn⟩ : ∃ (n : ℕ), Ideal.span {x^n} = Ideal.span {x^(n+1)}
      { obtain ⟨n, h⟩ := @IsArtinian.monotone_stabilizes _ _ _ _ _ ins1
          ⟨λ m ↦ OrderDual.toDual (Ideal.span {x^m}), λ m n h y hy ↦ by
            dsimp [OrderDual.toDual] at *
            rw [Ideal.mem_span_singleton] at hy ⊢
            obtain ⟨z, rfl⟩ := hy
            exact dvd_mul_of_dvd_left (pow_dvd_pow _ h) _⟩
        specialize h (n + 1) (by norm_num)
        exact ⟨n, h⟩ }
      have H : x^n ∈ Ideal.span {x^(n+1)} := by
      { rw [←hn]; exact Submodule.subset_span (Set.mem_singleton _) }
      rw [Ideal.mem_span_singleton] at H
      obtain ⟨y, hy⟩ := H
      rw [pow_add, mul_assoc, pow_one] at hy
      conv_lhs at hy => rw [←mul_one (x^n)]
      exact ⟨y, mul_left_cancel₀ (pow_ne_zero _ hx) hy.symm⟩ } }
