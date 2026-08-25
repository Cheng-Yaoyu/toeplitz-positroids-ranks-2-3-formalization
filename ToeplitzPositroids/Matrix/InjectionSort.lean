import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Sorting finite injections

This file gives the canonical factorization of an injection between finite ordinals into an
increasing injection followed by a permutation of its domain.  The factorization is packaged as
an equivalence, and the determinant lemmas at the end record the signs introduced by the
permutation.
-/

namespace ToeplitzPositroids

namespace InjectionSort

variable {r m : ℕ}

/-- The increasing injection obtained by sorting the values of `f`. -/
noncomputable def orderEmbedding (f : Fin r ↪ Fin m) : Fin r ↪o Fin m :=
  OrderEmbedding.ofStrictMono (f ∘ Tuple.sort f)
    ((Tuple.monotone_sort f).strictMono_of_injective
      (f.injective.comp (Tuple.sort f).injective))

/-- The permutation that reconstructs an injection from its sorted version. -/
noncomputable def permutation (f : Fin r ↪ Fin m) : Equiv.Perm (Fin r) :=
  (Tuple.sort f)⁻¹

@[simp]
theorem orderEmbedding_apply (f : Fin r ↪ Fin m) (i : Fin r) :
    orderEmbedding f i = f (Tuple.sort f i) :=
  rfl

@[simp]
theorem permutation_apply (f : Fin r ↪ Fin m) (i : Fin r) :
    permutation f i = (Tuple.sort f)⁻¹ i :=
  rfl

/-- Sorting does not change the range of an injection. -/
theorem range_orderEmbedding (f : Fin r ↪ Fin m) :
    Set.range (orderEmbedding f) = Set.range f := by
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Tuple.sort f i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(Tuple.sort f)⁻¹ i, by simp⟩

/-- An injection is its increasing rearrangement composed with its sorting permutation. -/
@[simp]
theorem orderEmbedding_comp_permutation (f : Fin r ↪ Fin m) :
    (orderEmbedding f : Fin r → Fin m) ∘ permutation f = f := by
  funext i
  simp

@[simp]
theorem orderEmbedding_permutation_apply (f : Fin r ↪ Fin m) (i : Fin r) :
    orderEmbedding f (permutation f i) = f i := by
  simpa only [Function.comp_apply] using congrFun (orderEmbedding_comp_permutation f) i

/-- Reconstruct an injection from an increasing injection and a permutation. -/
def ofOrderEmbeddingPerm (p : (Fin r ↪o Fin m) × Equiv.Perm (Fin r)) : Fin r ↪ Fin m :=
  p.2.toEmbedding.trans p.1.toEmbedding

@[simp]
theorem ofOrderEmbeddingPerm_apply (p : (Fin r ↪o Fin m) × Equiv.Perm (Fin r))
    (i : Fin r) :
    ofOrderEmbeddingPerm p i = p.1 (p.2 i) :=
  rfl

@[simp]
theorem orderEmbedding_ofOrderEmbeddingPerm
    (g : Fin r ↪o Fin m) (e : Equiv.Perm (Fin r)) :
    orderEmbedding (ofOrderEmbeddingPerm (g, e)) = g := by
  apply DFunLike.ext _ _
  intro i
  change g (e (Tuple.sort (g ∘ e) i)) = g i
  have hsorted : (g ∘ e) ∘ Tuple.sort (g ∘ e) = g := by
    rw [Tuple.comp_perm_comp_sort_eq_comp_sort]
    have hg : Tuple.sort (g : Fin r → Fin m) = Equiv.refl _ :=
      Tuple.sort_eq_refl_iff_monotone.mpr g.monotone
    rw [hg]
    rfl
  exact congrFun hsorted i

@[simp]
theorem permutation_ofOrderEmbeddingPerm
    (g : Fin r ↪o Fin m) (e : Equiv.Perm (Fin r)) :
    permutation (ofOrderEmbeddingPerm (g, e)) = e := by
  apply Equiv.ext
  intro i
  apply g.injective
  simpa only [orderEmbedding_ofOrderEmbeddingPerm, ofOrderEmbeddingPerm_apply] using
    orderEmbedding_permutation_apply (ofOrderEmbeddingPerm (g, e)) i

/-- Injections `Fin r ↪ Fin m` are canonically equivalent to an increasing injection together
with a permutation of `Fin r`. -/
noncomputable def equivOrderEmbeddingPerm :
    (Fin r ↪ Fin m) ≃ (Fin r ↪o Fin m) × Equiv.Perm (Fin r) where
  toFun f := (orderEmbedding f, permutation f)
  invFun := ofOrderEmbeddingPerm
  left_inv f := by
    apply Function.Embedding.ext
    intro i
    exact congrFun (orderEmbedding_comp_permutation f) i
  right_inv p := by
    rcases p with ⟨g, e⟩
    exact Prod.ext (orderEmbedding_ofOrderEmbeddingPerm g e)
      (permutation_ofOrderEmbeddingPerm g e)

@[simp]
theorem equivOrderEmbeddingPerm_apply (f : Fin r ↪ Fin m) :
    equivOrderEmbeddingPerm f = (orderEmbedding f, permutation f) :=
  rfl

@[simp]
theorem equivOrderEmbeddingPerm_symm_apply
    (p : (Fin r ↪o Fin m) × Equiv.Perm (Fin r)) :
    equivOrderEmbeddingPerm.symm p = ofOrderEmbeddingPerm p :=
  rfl

/-- The increasing injection and permutation in the reconstruction of `f` are unique. -/
theorem factorization_unique (f : Fin r ↪ Fin m) (g : Fin r ↪o Fin m)
    (e : Equiv.Perm (Fin r)) (h : (g : Fin r → Fin m) ∘ e = f) :
    g = orderEmbedding f ∧ e = permutation f := by
  have hEmbedding : ofOrderEmbeddingPerm (g, e) = f := by
    apply Function.Embedding.ext
    intro i
    exact congrFun h i
  have hPair := congrArg (equivOrderEmbeddingPerm (r := r) (m := m)) hEmbedding
  simpa only [equivOrderEmbeddingPerm_apply, orderEmbedding_ofOrderEmbeddingPerm,
    permutation_ofOrderEmbeddingPerm, Prod.mk.injEq] using hPair

/-- The determinant of a column selection by an arbitrary injection differs from that of the
increasing selection by the sign of its sorting permutation. -/
theorem det_submatrix_right (R : Type*) [CommRing R]
    (A : Matrix (Fin r) (Fin m) R) (f : Fin r ↪ Fin m) :
    (A.submatrix id f).det =
      Equiv.Perm.sign (permutation f) * (A.submatrix id (orderEmbedding f)).det := by
  rw [← Matrix.det_permute' (permutation f) (A.submatrix id (orderEmbedding f))]
  congr 1
  ext i j
  simp [Matrix.submatrix]

/-- The determinant of a row selection by an arbitrary injection differs from that of the
increasing selection by the sign of its sorting permutation. -/
theorem det_submatrix_left (R : Type*) [CommRing R]
    (A : Matrix (Fin m) (Fin r) R) (f : Fin r ↪ Fin m) :
    (A.submatrix f id).det =
      Equiv.Perm.sign (permutation f) * (A.submatrix (orderEmbedding f) id).det := by
  rw [← Matrix.det_permute (permutation f) (A.submatrix (orderEmbedding f) id)]
  congr 1
  ext i j
  simp [Matrix.submatrix]

end InjectionSort

end ToeplitzPositroids
