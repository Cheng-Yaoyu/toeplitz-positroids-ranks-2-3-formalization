import ToeplitzPositroids.Matrix.Configuration
import ToeplitzPositroids.Matrix.InjectionSort

/-!
# The finite rectangular Cauchy--Binet formula

This file proves Cauchy--Binet for matrices whose three index types are finite ordinals.  The
proof first expands the determinant as a sum over all functions selecting intermediate indices.
Noninjective selections have a repeated column and vanish.  Sorting each remaining injection
then groups its permutations into the second determinant in the formula.
-/

namespace ToeplitzPositroids

open scoped BigOperators

namespace Matrix

variable {R : Type*} [CommRing R]
variable {r m : ℕ}

/-- The direct determinant expansion of a rectangular product, before noninjective selections
are removed. -/
theorem det_mul_eq_sum_functions (A : Matrix (Fin r) (Fin m) R)
    (B : Matrix (Fin m) (Fin r) R) :
    (A * B).det =
      ∑ f : Fin r → Fin m, (A.submatrix id f).det * ∏ i, B (f i) i := by
  calc
    (A * B).det =
        ∑ f : Fin r → Fin m, ∑ σ : Equiv.Perm (Fin r),
          ((Equiv.Perm.sign σ : ℤ) : R) *
            ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
        Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ f : Fin r → Fin m, (A.submatrix id f).det * ∏ i, B (f i) i := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Matrix.det_apply', Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Matrix.submatrix_apply, Function.id_def, Finset.prod_mul_distrib]
      ring

/-- A noninjective column selection has zero determinant. -/
theorem det_submatrix_eq_zero_of_not_injective (A : Matrix (Fin r) (Fin m) R)
    (f : Fin r → Fin m) (hf : ¬Function.Injective f) :
    (A.submatrix id f).det = 0 := by
  simp only [Function.Injective] at hf
  push Not at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact Matrix.det_zero_of_column_eq hne fun k ↦ by simp [Matrix.submatrix, hij]

/-- The direct expansion may be restricted to bundled injections. -/
theorem det_mul_eq_sum_injections (A : Matrix (Fin r) (Fin m) R)
    (B : Matrix (Fin m) (Fin r) R) :
    (A * B).det =
      ∑ f : Fin r ↪ Fin m, (A.submatrix id f).det * ∏ i, B (f i) i := by
  rw [det_mul_eq_sum_functions]
  calc
    (∑ f : Fin r → Fin m, (A.submatrix id f).det * ∏ i, B (f i) i) =
        ∑ f : Fin r → Fin m with Function.Injective f,
          (A.submatrix id f).det * ∏ i, B (f i) i := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro f _ hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rw [det_submatrix_eq_zero_of_not_injective A f hf, zero_mul]
    _ = ∑ f : Fin r ↪ Fin m, (A.submatrix id f).det * ∏ i, B (f i) i := by
      classical
      exact Finset.sum_bij
        (fun f hf ↦ ⟨f, (Finset.mem_filter.mp hf).2⟩)
        (fun _ _ ↦ Finset.mem_univ _)
        (fun f₁ hf₁ f₂ hf₂ h ↦ by simpa using congrArg Function.Embedding.toFun h)
        (fun f _ ↦ ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.injective⟩, rfl⟩)
        (fun _ _ ↦ rfl)

/-- For a fixed increasing selection, summing over all its orderings produces the product of
the two corresponding minors. -/
theorem sum_permutations_eq_det_mul_det (A : Matrix (Fin r) (Fin m) R)
    (B : Matrix (Fin m) (Fin r) R) (cols : Fin r ↪o Fin m) :
    (∑ e : Equiv.Perm (Fin r),
        (A.submatrix id (InjectionSort.ofOrderEmbeddingPerm (cols, e))).det *
          ∏ i, B (InjectionSort.ofOrderEmbeddingPerm (cols, e) i) i) =
      (A.submatrix id cols).det * (B.submatrix cols id).det := by
  simp_rw [InjectionSort.det_submatrix_right R A,
    InjectionSort.orderEmbedding_ofOrderEmbeddingPerm,
    InjectionSort.permutation_ofOrderEmbeddingPerm,
    InjectionSort.ofOrderEmbeddingPerm_apply]
  rw [Matrix.det_apply' (B.submatrix cols id), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Matrix.submatrix_apply, Function.id_def]
  ring

/-- **Cauchy--Binet.** The determinant of a finite rectangular product is the sum of products
of its complementary ordered maximal minors. -/
theorem det_mul_eq_sum_orderedMinor (A : Matrix (Fin r) (Fin m) R)
    (B : Matrix (Fin m) (Fin r) R) :
    (A * B).det =
      ∑ cols : Fin r ↪o Fin m,
        orderedMinor A (allRows r) cols * orderedMinor B cols (allRows r) := by
  rw [det_mul_eq_sum_injections]
  calc
    (∑ f : Fin r ↪ Fin m, (A.submatrix id f).det * ∏ i, B (f i) i) =
        ∑ p : (Fin r ↪o Fin m) × Equiv.Perm (Fin r),
          (A.submatrix id (InjectionSort.ofOrderEmbeddingPerm p)).det *
            ∏ i, B (InjectionSort.ofOrderEmbeddingPerm p i) i := by
      apply Fintype.sum_equiv InjectionSort.equivOrderEmbeddingPerm
      intro f
      have hf : InjectionSort.ofOrderEmbeddingPerm
          (InjectionSort.orderEmbedding f, InjectionSort.permutation f) = f := by
        apply Function.Embedding.ext
        intro i
        exact InjectionSort.orderEmbedding_permutation_apply f i
      rw [InjectionSort.equivOrderEmbeddingPerm_apply]
      rw [hf]
    _ = ∑ cols : Fin r ↪o Fin m,
          (A.submatrix id cols).det * (B.submatrix cols id).det := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro cols _
      exact sum_permutations_eq_det_mul_det A B cols
    _ = ∑ cols : Fin r ↪o Fin m,
          orderedMinor A (allRows r) cols * orderedMinor B cols (allRows r) := by
      apply Finset.sum_congr rfl
      intro cols _
      simp [orderedMinor, allRows]

end Matrix

end ToeplitzPositroids
