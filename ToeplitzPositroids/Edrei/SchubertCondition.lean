import ToeplitzPositroids.Edrei.IndexTuple
import Mathlib.Data.Finset.Image
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# The Schubert condition for the first-row Edrei block

This file formalizes the arithmetic part of Corollary 24.  We use both the manuscript's
one-based increasing tuples and increasing selections `Fin r ↪o Fin n`.  No analytic assumptions
on Edrei specializations enter here.
-/

namespace ToeplitzPositroids.Edrei

private theorem strictMono_fin_add_le {r : ℕ} {f : Fin r → ℕ}
    (hf : StrictMono f) (i : Fin r) (k : ℕ) (hbound : i.val + k < r) :
    k + f i ≤ f ⟨i.val + k, hbound⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : i.val + k < r := by omega
      have hprev := ih hk
      have hstep : f ⟨i.val + k, hk⟩ < f ⟨i.val + (k + 1), hbound⟩ := by
        apply hf
        exact Fin.mk_lt_mk.mpr (by omega)
      omega

/-- The position in the original tuple corresponding to a hook inequality. -/
def hookPosition (r p : ℕ) (l : Fin (r - p)) : Fin r :=
  ⟨l.val, lt_of_lt_of_le l.isLt (Nat.sub_le r p)⟩

/-- The family `j_l ≤ l+q`, written with zero-based `Fin` positions and one-based values. -/
def HookInequalityFamily {r : ℕ} (J : IncreasingIndexTuple r) (p q : ℕ) : Prop :=
  ∀ l : Fin (r - p), J (hookPosition r p l) ≤ l.val + 1 + q

/-- The same family with the manuscript's explicit one-based quantifier
`1 ≤ l ≤ r-p`. -/
def OneBasedHookInequalityFamily {r : ℕ} (J : IncreasingIndexTuple r)
    (p q : ℕ) : Prop :=
  ∀ (l : ℕ) (hl : 1 ≤ l) (hupper : l ≤ r - p),
    J ⟨l - 1, by omega⟩ ≤ l + q

theorem oneBasedHookInequalityFamily_iff {r : ℕ} (J : IncreasingIndexTuple r)
    (p q : ℕ) :
    OneBasedHookInequalityFamily J p q ↔ HookInequalityFamily J p q := by
  constructor
  · intro h l
    have hl := h (l.val + 1) (by omega) (by omega)
    exact hl
  · intro h l hl hupper
    let k : Fin (r - p) := ⟨l - 1, by omega⟩
    have hk := h k
    change J ⟨l - 1, by omega⟩ ≤ l - 1 + 1 + q at hk
    change J ⟨l - 1, by omega⟩ ≤ l + q
    omega

/-- The final inequality `j_{r-p} ≤ r-p+q`, defined when `p < r`. -/
def LastHookInequality {r : ℕ} (J : IncreasingIndexTuple r) (p q : ℕ)
    (hp : p < r) : Prop :=
  J ⟨r - p - 1, by omega⟩ ≤ r - p + q

/-- Strict increase makes the whole hook-inequality family equivalent to its last member. -/
theorem hookInequalityFamily_iff_last {r : ℕ} (J : IncreasingIndexTuple r)
    (p q : ℕ) (hp : p < r) :
    HookInequalityFamily J p q ↔ LastHookInequality J p q hp := by
  constructor
  · intro h
    let l : Fin (r - p) := ⟨r - p - 1, by omega⟩
    have hl := h l
    change J ⟨r - p - 1, by omega⟩ ≤ r - p - 1 + 1 + q at hl
    change J ⟨r - p - 1, by omega⟩ ≤ r - p + q
    omega
  · intro hlast l
    let k := hookPosition r p l
    let last : Fin r := ⟨r - p - 1, by omega⟩
    have hklast : k.val ≤ last.val := by
      simp only [k, last, hookPosition]
      omega
    have hgap := strictMono_fin_add_le J.strictMono k (last.val - k.val) (by
      rw [Nat.add_sub_of_le hklast]
      exact last.isLt)
    have hindex : (⟨k.val + (last.val - k.val), by omega⟩ : Fin r) = last := by
      apply Fin.ext
      exact Nat.add_sub_of_le hklast
    rw [hindex] at hgap
    have hlast' : J last ≤ r - p + q := by
      simpa [LastHookInequality, last] using hlast
    have hdiff : last.val - k.val + k.val = last.val := Nat.sub_add_cancel hklast
    have hlastVal : last.val + 1 = r - p := by
      simp only [last]
      omega
    have hkVal : k.val = l.val := rfl
    change J k ≤ l.val + 1 + q
    omega

/-- The explicitly one-based family is likewise equivalent to its final inequality. -/
theorem oneBasedHookInequalityFamily_iff_last {r : ℕ} (J : IncreasingIndexTuple r)
    (p q : ℕ) (hp : p < r) :
    OneBasedHookInequalityFamily J p q ↔ LastHookInequality J p q hp :=
  (oneBasedHookInequalityFamily_iff J p q).trans
    (hookInequalityFamily_iff_last J p q hp)

/-- When `p ≥ r`, the hook family is empty and hence automatic. -/
theorem hookInequalityFamily_of_rank_le_p {r : ℕ} (J : IncreasingIndexTuple r)
    {p q : ℕ} (hrp : r ≤ p) :
    HookInequalityFamily J p q := by
  intro l
  exact Fin.elim0 (Fin.cast (by omega) l)

/-- Convert an increasing finite selection to the manuscript's one-based tuple. -/
def oneBasedIndexTuple {r n : ℕ} (J : Fin r ↪o Fin n) : IncreasingIndexTuple r where
  value k := (J k).val + 1
  strictMono := by
    intro i j hij
    have h := J.strictMono hij
    change (J i).val < (J j).val at h
    change (J i).val + 1 < (J j).val + 1
    omega
  position_le := by
    intro k
    let z : Fin r := ⟨0, by have := k.isLt; omega⟩
    by_cases hk : k.val = 0
    · omega
    · have hgap := strictMono_fin_add_le J.strictMono z k.val (by simp [z])
      have heq : (⟨0 + k.val, by omega⟩ : Fin r) = k := by
        apply Fin.ext
        simp
      rw [heq] at hgap
      simp only [z] at hgap
      omega

/-- The Schubert hook family for an increasing `r`-subset of `Fin n`. -/
def SelectionHookCondition {r n : ℕ} (J : Fin r ↪o Fin n) (p q : ℕ) : Prop :=
  HookInequalityFamily (oneBasedIndexTuple J) p q

/-- Its last inequality in zero-based selection notation. -/
def SelectionLastCondition {r n : ℕ} (J : Fin r ↪o Fin n) (p q : ℕ)
    (hp : p < r) : Prop :=
  (J ⟨r - p - 1, by omega⟩).val + 1 ≤ r - p + q

theorem selectionHookCondition_iff_last {r n : ℕ} (J : Fin r ↪o Fin n)
    (p q : ℕ) (hp : p < r) :
    SelectionHookCondition J p q ↔ SelectionLastCondition J p q hp := by
  exact hookInequalityFamily_iff_last (oneBasedIndexTuple J) p q hp

/-! ## Cardinality form -/

/-- The finite set of selected zero-based column indices. -/
def selectedFinset {r n : ℕ} (J : Fin r ↪o Fin n) : Finset (Fin n) :=
  Finset.univ.map J.toEmbedding

/-- The one-based initial interval `[1,T]`, represented inside `Fin n`. -/
def oneBasedInitialSegment (n T : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j.val + 1 ≤ T

/-- The cardinality condition `|J ∩ [1,r-p+q]| ≥ r-p`. -/
def SelectionCardinalityCondition {r n : ℕ} (J : Fin r ↪o Fin n)
    (p q : ℕ) : Prop :=
  r - p ≤ (selectedFinset J ∩ oneBasedInitialSegment n (r - p + q)).card

/-- Positions strictly before `s`. -/
def positionPrefix (r s : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun k ↦ k.val < s

theorem card_positionPrefix {r s : ℕ} (hs : s ≤ r) :
    (positionPrefix r s).card = s := by
  classical
  let e := Fin.castLEOrderIso hs
  have hcard := Fintype.card_congr e.toEquiv
  rw [Fintype.card_fin] at hcard
  rw [positionPrefix, ← Fintype.card_subtype (fun k : Fin r ↦ k.val < s)]
  exact hcard.symm

/-- Filtering the selected values is cardinality-equivalent to filtering their positions. -/
theorem card_selected_inter_initial_eq_filter_positions {r n T : ℕ}
    (J : Fin r ↪o Fin n) :
    (selectedFinset J ∩ oneBasedInitialSegment n T).card =
      (Finset.univ.filter fun k : Fin r ↦ (J k).val + 1 ≤ T).card := by
  classical
  have hfinset : selectedFinset J ∩ oneBasedInitialSegment n T =
      (Finset.univ.filter fun k : Fin r ↦ (J k).val + 1 ≤ T).map J.toEmbedding := by
    ext x
    simp only [selectedFinset, oneBasedInitialSegment, Finset.mem_inter, Finset.mem_map,
      Finset.mem_univ, Finset.mem_filter, true_and]
    constructor
    · rintro ⟨⟨a, rfl⟩, ha⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, ha⟩
  rw [hfinset, Finset.card_map]

/-- The last hook inequality is equivalent to the cardinality rank condition. -/
theorem selectionLastCondition_iff_cardinality {r n : ℕ} (J : Fin r ↪o Fin n)
    (p q : ℕ) (hp : p < r) :
    SelectionLastCondition J p q hp ↔ SelectionCardinalityCondition J p q := by
  let s := r - p
  let T := s + q
  let last : Fin r := ⟨s - 1, by dsimp only [s]; omega⟩
  have hspos : 0 < s := by dsimp only [s]; omega
  have hsr : s ≤ r := by dsimp only [s]; exact Nat.sub_le r p
  rw [SelectionCardinalityCondition,
    card_selected_inter_initial_eq_filter_positions]
  change (J last).val + 1 ≤ T ↔
    s ≤ (Finset.univ.filter fun k : Fin r ↦ (J k).val + 1 ≤ T).card
  constructor
  · intro hlast
    have hsubset : positionPrefix r s ⊆
        Finset.univ.filter fun k : Fin r ↦ (J k).val + 1 ≤ T := by
      intro k hk
      simp only [positionPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      have hklast : k ≤ last := by
        change k.val ≤ s - 1
        omega
      have hmono := J.monotone hklast
      change (J k).val ≤ (J last).val at hmono
      omega
    have hcard := Finset.card_le_card hsubset
    rw [card_positionPrefix hsr] at hcard
    exact hcard
  · intro hcard
    by_contra hlast
    have hsubset : (Finset.univ.filter fun k : Fin r ↦ (J k).val + 1 ≤ T) ⊆
        positionPrefix r (s - 1) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp only [positionPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hkpos
      have hlastk : last ≤ k := by
        change s - 1 ≤ k.val
        omega
      have hmono := J.monotone hlastk
      change (J last).val ≤ (J k).val at hmono
      omega
    have hsmall := Finset.card_le_card hsubset
    rw [card_positionPrefix (show s - 1 ≤ r by omega)] at hsmall
    omega

/-- The three manuscript formulations are equivalent. -/
theorem selectionHookCondition_iff_cardinality {r n : ℕ} (J : Fin r ↪o Fin n)
    (p q : ℕ) (hp : p < r) :
    SelectionHookCondition J p q ↔ SelectionCardinalityCondition J p q :=
  (selectionHookCondition_iff_last J p q hp).trans
    (selectionLastCondition_iff_cardinality J p q hp)

/-! ## Uniform regimes -/

/-- The universal order-statistic bound for an increasing `r`-subset of `Fin n`:
`j_l ≤ n-r+l` in one-based notation. -/
theorem oneBasedSelection_value_le {r n : ℕ} (J : Fin r ↪o Fin n) (k : Fin r) :
    (J k).val + 1 ≤ k.val + 1 + (n - r) := by
  have hrn : r ≤ n := by
    have hcard := Fintype.card_le_of_injective J J.injective
    simpa using hcard
  have hnr : n - r + r = n := Nat.sub_add_cancel hrn
  let last : Fin r := ⟨r - 1, by have := k.isLt; omega⟩
  have hklast : k.val ≤ last.val := by
    simp only [last]
    omega
  have hgap := strictMono_fin_add_le J.strictMono k (last.val - k.val) (by
    rw [Nat.add_sub_of_le hklast]
    exact last.isLt)
  have hindex : (⟨k.val + (last.val - k.val), by omega⟩ : Fin r) = last := by
    apply Fin.ext
    exact Nat.add_sub_of_le hklast
  rw [hindex] at hgap
  have hlastBound := (J last).isLt
  have hdiff : last.val - k.val + k.val = last.val := Nat.sub_add_cancel hklast
  have hlastVal : last.val + 1 = r := by simp [last]; omega
  omega

/-- If `q ≥ n-r`, every hook inequality is automatic. -/
theorem selectionHookCondition_of_codimension_le_q {r n : ℕ} (J : Fin r ↪o Fin n)
    (p q : ℕ) (hq : n - r ≤ q) :
    SelectionHookCondition J p q := by
  intro l
  change (J (hookPosition r p l)).val + 1 ≤ l.val + 1 + q
  have hbound := oneBasedSelection_value_le J (hookPosition r p l)
  change (J (hookPosition r p l)).val + 1 ≤ l.val + 1 + (n - r) at hbound
  omega

/-- If `p ≥ r`, every selection satisfies both the empty family and cardinality condition. -/
theorem selectionConditions_of_rank_le_p {r n : ℕ} (J : Fin r ↪o Fin n)
    {p q : ℕ} (hrp : r ≤ p) :
    SelectionHookCondition J p q ∧ SelectionCardinalityCondition J p q := by
  constructor
  · exact hookInequalityFamily_of_rank_le_p (oneBasedIndexTuple J) hrp
  · unfold SelectionCardinalityCondition
    simp [Nat.sub_eq_zero_of_le hrp]

/-- If `q ≥ n-r`, every selection satisfies both equivalent Schubert conditions. -/
theorem selectionConditions_of_codimension_le_q {r n : ℕ} (J : Fin r ↪o Fin n)
    (p q : ℕ) (hq : n - r ≤ q) :
    SelectionHookCondition J p q ∧ SelectionCardinalityCondition J p q := by
  have hhook := selectionHookCondition_of_codimension_le_q J p q hq
  refine ⟨hhook, ?_⟩
  by_cases hp : p < r
  · exact (selectionHookCondition_iff_cardinality J p q hp).mp hhook
  · exact (selectionConditions_of_rank_le_p J (Nat.le_of_not_gt hp)).2

/-- The Schubert basis predicate on increasing `r`-subsets of `Fin n`. -/
def SchubertBasisPredicate (r n p q : ℕ) : (Fin r ↪o Fin n) → Prop :=
  fun J ↦ SelectionCardinalityCondition J p q

/-- The uniform basis predicate accepts every increasing `r`-subset. -/
def UniformBasisPredicate (r n : ℕ) : (Fin r ↪o Fin n) → Prop :=
  fun _ ↦ True

/-- The Schubert predicate is uniform when `p ≥ r`. -/
theorem schubertBasisPredicate_eq_uniform_of_rank_le_p
    (r n p q : ℕ) (hrp : r ≤ p) :
    SchubertBasisPredicate r n p q = UniformBasisPredicate r n := by
  funext J
  apply propext
  constructor
  · exact fun _ ↦ True.intro
  · exact fun _ ↦ (selectionConditions_of_rank_le_p J hrp).2

/-- The Schubert predicate is uniform when `q ≥ n-r`. -/
theorem schubertBasisPredicate_eq_uniform_of_codimension_le_q
    (r n p q : ℕ) (hq : n - r ≤ q) :
    SchubertBasisPredicate r n p q = UniformBasisPredicate r n := by
  funext J
  apply propext
  constructor
  · exact fun _ ↦ True.intro
  · exact fun _ ↦ (selectionConditions_of_codimension_le_q J p q hq).2

end ToeplitzPositroids.Edrei
