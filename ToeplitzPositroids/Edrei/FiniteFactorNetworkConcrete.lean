import ToeplitzPositroids.Edrei.FiniteFactorNetworkTransfer
import ToeplitzPositroids.Edrei.ExponentialMinor

/-!
# Transfer entries and path sums for the finite-factor network

The truncated Toeplitz representation turns multiplication of power series into matrix
multiplication.  It identifies the complete chip transfer matrix with the finite Edrei factor.
A recursive trajectory model then proves that each transfer entry is exactly the weighted sum of
the valid network paths with those endpoints.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids Matrix

noncomputable def psToeplitz (N : ℕ) (f : PowerSeries ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun x y ↦ if x.val ≤ y.val then PowerSeries.coeff (y.val - x.val) f else 0

theorem psToeplitz_mul (N : ℕ) (f g : PowerSeries ℝ) :
    psToeplitz N (f * g) = psToeplitz N f * psToeplitz N g := by
  ext x y
  rw [Matrix.mul_apply]
  by_cases hxy : x.val ≤ y.val
  · rw [psToeplitz, if_pos hxy, PowerSeries.coeff_mul]
    simp only [psToeplitz]
    let s := Finset.univ.filter fun z : Fin (N + 1) ↦ x.val ≤ z.val ∧ z.val ≤ y.val
    have hsum :
        (∑ z ∈ s, PowerSeries.coeff (z.val - x.val) f *
            PowerSeries.coeff (y.val - z.val) g) =
          ∑ ab ∈ Finset.antidiagonal (y.val - x.val),
            PowerSeries.coeff ab.1 f * PowerSeries.coeff ab.2 g := by
      apply Finset.sum_bij
        (fun z hz ↦ (z.val - x.val, y.val - z.val))
      · intro z hz
        rw [Finset.mem_antidiagonal]
        have hz' := (Finset.mem_filter.mp hz).2
        omega
      · intro z₁ hz₁ z₂ hz₂ heq
        apply Fin.ext
        have h₁ := congrArg Prod.fst heq
        have hz₁' := (Finset.mem_filter.mp hz₁).2
        have hz₂' := (Finset.mem_filter.mp hz₂).2
        dsimp at h₁
        omega
      · intro ab hab
        have hab' := Finset.mem_antidiagonal.mp hab
        let z : Fin (N + 1) := ⟨x.val + ab.1, by omega⟩
        refine ⟨z, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [z]; omega⟩
        · apply Prod.ext <;> dsimp [z] <;> omega
      · intro z hz
        rfl
    rw [← hsum]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hz' : x.val ≤ z.val ∧ z.val ≤ y.val
    · simp [hz'.1, hz'.2]
    · rcases not_and_or.mp hz' with hxz | hzy
      · simp [hxz]
      · simp [hzy]
  · rw [psToeplitz, if_neg hxy]
    symm
    apply Finset.sum_eq_zero
    intro z hz
    simp only [psToeplitz]
    by_cases hxz : x.val ≤ z.val
    · have hzy : ¬z.val ≤ y.val := by omega
      simp [hxz, hzy]
    · simp [hxz]

def chip (N k : ℕ) (a : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun x y ↦ if x = y then 1 else if x.val = k ∧ y.val = x.val + 1 then a else 0

def chipPrefix (N : ℕ) (a : ℝ) : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => 1
  | k + 1 => chipPrefix N a k * chip N k a

theorem chipPrefix_apply (N : ℕ) (a : ℝ) {L : ℕ} (hL : L ≤ N)
    (x y : Fin (N + 1)) :
    chipPrefix N a L x y =
      if x.val = y.val then 1 else
        if x.val < y.val ∧ y.val ≤ L then a ^ (y.val - x.val) else 0 := by
  induction L generalizing x y with
  | zero =>
      rw [chipPrefix]
      change (if x = y then 1 else 0) = _
      by_cases hxy : x = y
      · subst y
        simp
      · have hval : x.val ≠ y.val := by simpa [Fin.ext_iff] using hxy
        rw [if_neg hxy, if_neg hval, if_neg]
        rintro ⟨hlt, hy⟩
        omega
  | succ L ih =>
      rw [chipPrefix, Matrix.mul_apply]
      simp_rw [ih (Nat.le_of_succ_le hL)]
      let k : Fin (N + 1) := ⟨L, by omega⟩
      let ks : Fin (N + 1) := ⟨L + 1, by omega⟩
      have hchip (z : Fin (N + 1)) : chip N L a z y =
          if z = y then 1 else if z = k ∧ y = ks then a else 0 := by
        simp only [chip]
        by_cases hzy : z = y
        · simp [hzy]
        · rw [if_neg hzy, if_neg hzy]
          congr 1
          apply propext
          constructor
          · rintro ⟨hz, hy⟩
            constructor
            · apply Fin.ext
              simpa [k] using hz
            · apply Fin.ext
              dsimp [ks]
              omega
          · rintro ⟨hz, hy⟩
            constructor
            · simpa [k] using congrArg Fin.val hz
            · have hzv := congrArg Fin.val hz
              have hyv := congrArg Fin.val hy
              dsimp [k, ks] at hzv hyv
              omega
      simp_rw [hchip]
      change (∑ z ∈ Finset.univ,
        (if x.val = z.val then 1
          else if x.val < z.val ∧ z.val ≤ L then a ^ (z.val - x.val) else 0) *
        (if z = y then 1 else if z = k ∧ y = ks then a else 0)) = _
      rw [Finset.sum_eq_add_sum_diff_singleton y _ (by simp)]
      simp only [if_pos, mul_one]
      have herase :
          (∑ z ∈ Finset.univ \ {y},
            (if x.val = z.val then 1
              else if x.val < z.val ∧ z.val ≤ L then a ^ (z.val - x.val) else 0) *
            (if z = y then 1 else if z = k ∧ y = ks then a else 0)) =
          ∑ z ∈ Finset.univ \ {y},
            (if x.val = z.val then 1
              else if x.val < z.val ∧ z.val ≤ L then a ^ (z.val - x.val) else 0) *
            if z = k ∧ y = ks then a else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzy : z ≠ y := by
          simpa using (Finset.mem_sdiff.mp hz).2
        simp [hzy]
      rw [herase]
      by_cases hy : y = ks
      · subst y
        have hky : k ≠ ks := by simp [k, ks, Fin.ext_iff]
        rw [Finset.sum_eq_add_sum_diff_singleton
          (s := Finset.univ \ {ks}) k _ (by simp [hky])]
        simp only [true_and, if_pos]
        have hrest :
            (∑ z ∈ (Finset.univ \ {ks}) \ {k},
              (if x.val = z.val then 1
                else if x.val < z.val ∧ z.val ≤ L then a ^ (z.val - x.val) else 0) *
              if z = k ∧ ks = ks then a else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          have hzk : z ≠ k := by
            simpa using (Finset.mem_sdiff.mp hz).2
          simp [hzk]
        simp only [and_true] at hrest ⊢
        rw [hrest, add_zero]
        dsimp only [k, ks]
        by_cases hxL : x.val = L + 1
        · simp [hxL]
        by_cases hxlt : x.val < L + 1
        · have hxle : x.val ≤ L := by omega
          simp [hxL, hxlt, pow_succ', Nat.sub_add_comm hxle]
          by_cases hxEq : x.val = L
          · simp [hxEq]
          · have hxLess : x.val < L := lt_of_le_of_ne hxle hxEq
            simp [hxEq, hxLess, mul_comm]
        · have hxgt : L + 1 < x.val := by omega
          have hxNe : x.val ≠ L := by omega
          have hxNotLt : ¬x.val < L := by omega
          simp [hxL, hxlt, hxNe, hxNotLt]
      · have hyk : y ≠ ks := hy
        have hrest :
            (∑ z ∈ Finset.univ \ {y},
              (if x.val = z.val then 1
                else if x.val < z.val ∧ z.val ≤ L then a ^ (z.val - x.val) else 0) *
              if z = k ∧ y = ks then a else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro z hz
          simp [hyk]
        rw [hrest, add_zero]
        have hyNotSucc : y.val ≠ L + 1 := by
          intro heq
          apply hy
          apply Fin.ext
          simpa [ks]
        have hle : y.val ≤ L ↔ y.val ≤ L + 1 := by omega
        by_cases hxy : x.val = y.val
        · simp [hxy]
        · by_cases hxylt : x.val < y.val
          · by_cases hyL : y.val ≤ L
            · have hyLs : y.val ≤ L + 1 := hle.mp hyL
              simp [hxy, hxylt, hyL, hyLs]
            · have hyLs : ¬y.val ≤ L + 1 := mt hle.mpr hyL
              simp [hxy, hxylt, hyL, hyLs]
          · simp [hxy, hxylt]

theorem chipPrefix_eq_psToeplitz_alpha (N : ℕ) (a : ℝ) :
    chipPrefix N a N = psToeplitz N (ToeplitzPositroids.FiniteEdreiData.alphaFactor a) := by
  ext x y
  rw [chipPrefix_apply N a (le_refl N)]
  simp only [psToeplitz, ToeplitzPositroids.FiniteEdreiData.coeff_alphaFactor]
  by_cases hxy : x.val = y.val
  · simp [hxy]
  · by_cases hlt : x.val < y.val
    · have hle : x.val ≤ y.val := hlt.le
      simp [hxy, hlt, hle, Nat.le_of_lt_succ y.isLt]
    · have hgt : y.val < x.val := by omega
      have hnle : ¬x.val ≤ y.val := by omega
      simp [hxy, hlt, hnle]

theorem networkStageMatrix_alpha_chip {p q N : ℕ} (D : FiniteEdreiData p q)
    (a : Fin p) (k : Fin N) :
    FiniteEdreiData.networkStageMatrix D N (q + a.val * N + k.val) =
      chip N k.val (D.alpha a) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h ↦ by simpa [h] using k.isLt
  have hkdiv : k.val / N = 0 := Nat.div_eq_of_lt k.isLt
  have hdiv : (a.val * N + k.val) / N = a.val := by
    rw [Nat.mul_comm a.val N, Nat.mul_add_div hN, hkdiv, add_zero]
  have hmod : (a.val * N + k.val) % N = k.val := by
    rw [Nat.mul_comm a.val N, Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]
  ext x y
  unfold FiniteEdreiData.networkStageMatrix FiniteEdreiData.networkStepWeight chip
  have ht : ¬q + a.val * N + k.val < q := by omega
  rw [dif_neg ht]
  have hsub : q + a.val * N + k.val - q = a.val * N + k.val := by omega
  rw [hsub]
  dsimp only
  rw [hdiv, hmod]
  simp only [dif_pos a.isLt]
  by_cases hxy : y.val = x.val
  · have hxy' : x = y := by apply Fin.ext; omega
    simp [hxy, hxy']
  · have hxy' : x ≠ y := by
      intro h
      apply hxy
      simp [h]
    simp [hxy, hxy']

theorem networkStageMatrix_beta_psToeplitz {p q N : ℕ} (D : FiniteEdreiData p q)
    (t : Fin q) :
    FiniteEdreiData.networkStageMatrix D N t.val =
      psToeplitz N (FiniteEdreiData.betaFactor (D.beta t)) := by
  ext x y
  unfold FiniteEdreiData.networkStageMatrix FiniteEdreiData.networkStepWeight psToeplitz
  rw [dif_pos t.isLt]
  by_cases hstay : y.val = x.val
  · simp [hstay, FiniteEdreiData.betaFactor]
  · rw [if_neg hstay]
    by_cases hstep : y.val = x.val + 1
    · have hle : x.val ≤ y.val := by omega
      simp [hstep, FiniteEdreiData.betaFactor]
    · by_cases hle : x.val ≤ y.val
      · have hdiff : 2 ≤ y.val - x.val := by omega
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hdiff
        rw [hd]
        have hcoeff : PowerSeries.coeff (2 + d)
            (FiniteEdreiData.betaFactor (D.beta t)) = 0 := by
          simp [FiniteEdreiData.betaFactor, PowerSeries.coeff_X]
          omega
        simp [hstep, hle, hcoeff]
      · simp [hstep, hle]

@[simp]
theorem psToeplitz_one (N : ℕ) : psToeplitz N (1 : PowerSeries ℝ) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [psToeplitz]
  · have hval : x.val ≠ y.val := by simpa [Fin.ext_iff] using hxy
    by_cases hle : x.val ≤ y.val
    · have hpos : 0 < y.val - x.val := by omega
      simp [psToeplitz, hxy, hle, PowerSeries.coeff_one, hpos.ne']
    · simp [psToeplitz, hxy, hle]

/-- Product of `K` consecutive stage matrices beginning at stage `start`. -/
def FiniteEdreiData.networkStageProductFrom {p q : ℕ} (D : FiniteEdreiData p q)
    (N start : ℕ) : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => 1
  | K + 1 => FiniteEdreiData.networkStageProductFrom D N start K *
      FiniteEdreiData.networkStageMatrix D N (start + K)

theorem FiniteEdreiData.networkTransferPrefix_add {p q : ℕ}
    (D : FiniteEdreiData p q) (N L K : ℕ) :
    FiniteEdreiData.networkTransferPrefix D N (L + K) =
      FiniteEdreiData.networkTransferPrefix D N L *
        FiniteEdreiData.networkStageProductFrom D N L K := by
  induction K with
  | zero => simp [FiniteEdreiData.networkStageProductFrom]
  | succ K ih =>
      change FiniteEdreiData.networkTransferPrefix D N ((L + K) + 1) =
        FiniteEdreiData.networkTransferPrefix D N L *
          (FiniteEdreiData.networkStageProductFrom D N L K *
            FiniteEdreiData.networkStageMatrix D N (L + K))
      rw [FiniteEdreiData.networkTransferPrefix, ih, Matrix.mul_assoc]

theorem FiniteEdreiData.networkAlphaBlockPrefix_eq_chipPrefix {p q N : ℕ}
    (D : FiniteEdreiData p q) (a : Fin p) {L : ℕ} (hL : L ≤ N) :
    FiniteEdreiData.networkStageProductFrom D N (q + a.val * N) L =
      chipPrefix N (D.alpha a) L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      rw [FiniteEdreiData.networkStageProductFrom, chipPrefix,
        ih (Nat.le_of_succ_le hL)]
      let k : Fin N := ⟨L, by omega⟩
      have hstage := networkStageMatrix_alpha_chip D a k
      dsimp only [k] at hstage
      simpa [Nat.add_assoc] using congrArg
        (fun M ↦ chipPrefix N (D.alpha a) L * M) hstage

theorem FiniteEdreiData.networkAlphaBlock_eq_psToeplitz {p q N : ℕ}
    (D : FiniteEdreiData p q) (a : Fin p) :
    FiniteEdreiData.networkStageProductFrom D N (q + a.val * N) N =
      psToeplitz N (FiniteEdreiData.alphaFactor (D.alpha a)) := by
  rw [FiniteEdreiData.networkAlphaBlockPrefix_eq_chipPrefix D a (le_refl N),
    chipPrefix_eq_psToeplitz_alpha]

/-- Product of the first `L` beta-factor series, with harmless totalization past `q`. -/
noncomputable def FiniteEdreiData.betaPrefixSeries {p q : ℕ} (D : FiniteEdreiData p q)
    (L : ℕ) : PowerSeries ℝ :=
  ∏ j ∈ Finset.range L,
    if h : j < q then FiniteEdreiData.betaFactor (D.beta ⟨j, h⟩) else 1

theorem FiniteEdreiData.networkBetaPrefix_eq_psToeplitz {p q N : ℕ}
    (D : FiniteEdreiData p q) {L : ℕ} (hL : L ≤ q) :
    FiniteEdreiData.networkTransferPrefix D N L =
      psToeplitz N (FiniteEdreiData.betaPrefixSeries D L) := by
  induction L with
  | zero => simp [FiniteEdreiData.networkTransferPrefix, FiniteEdreiData.betaPrefixSeries]
  | succ L ih =>
      have hLq : L < q := by omega
      rw [FiniteEdreiData.networkTransferPrefix, ih (Nat.le_of_succ_le hL),
        networkStageMatrix_beta_psToeplitz D ⟨L, hLq⟩, ← psToeplitz_mul]
      simp [FiniteEdreiData.betaPrefixSeries, Finset.prod_range_succ, hLq]

theorem FiniteEdreiData.betaPrefixSeries_eq_betaProduct {p q : ℕ}
    (D : FiniteEdreiData p q) :
    FiniteEdreiData.betaPrefixSeries D q = D.betaProduct := by
  rw [FiniteEdreiData.betaPrefixSeries, Finset.prod_range]
  simp [FiniteEdreiData.betaProduct]

theorem FiniteEdreiData.networkBetaTransfer_eq_psToeplitz {p q N : ℕ}
    (D : FiniteEdreiData p q) :
    FiniteEdreiData.networkTransferPrefix D N q = psToeplitz N D.betaProduct := by
  rw [FiniteEdreiData.networkBetaPrefix_eq_psToeplitz D (le_refl q),
    FiniteEdreiData.betaPrefixSeries_eq_betaProduct D]

/-- Product of the first `A` alpha-factor series, totalized past `p`. -/
noncomputable def FiniteEdreiData.alphaPrefixSeries {p q : ℕ} (D : FiniteEdreiData p q)
    (A : ℕ) : PowerSeries ℝ :=
  ∏ i ∈ Finset.range A,
    if h : i < p then FiniteEdreiData.alphaFactor (D.alpha ⟨i, h⟩) else 1

theorem FiniteEdreiData.networkFactorPrefix_eq_psToeplitz {p q N : ℕ}
    (D : FiniteEdreiData p q) {A : ℕ} (hA : A ≤ p) :
    FiniteEdreiData.networkTransferPrefix D N (q + A * N) =
      psToeplitz N (D.betaProduct * FiniteEdreiData.alphaPrefixSeries D A) := by
  induction A with
  | zero =>
      simp [FiniteEdreiData.networkBetaTransfer_eq_psToeplitz D,
        FiniteEdreiData.alphaPrefixSeries]
  | succ A ih =>
      have hAp : A < p := by omega
      let a : Fin p := ⟨A, hAp⟩
      have hadd := FiniteEdreiData.networkTransferPrefix_add D N (q + A * N) N
      have hblock := FiniteEdreiData.networkAlphaBlock_eq_psToeplitz (N := N) D a
      dsimp only [a] at hblock
      rw [Nat.succ_mul, ← Nat.add_assoc]
      rw [hadd, ih (Nat.le_of_succ_le hA), hblock, ← psToeplitz_mul]
      simp [FiniteEdreiData.alphaPrefixSeries, Finset.prod_range_succ, hAp,
        mul_assoc]

theorem FiniteEdreiData.alphaPrefixSeries_eq_alphaProduct {p q : ℕ}
    (D : FiniteEdreiData p q) :
    FiniteEdreiData.alphaPrefixSeries D p = D.alphaProduct := by
  rw [FiniteEdreiData.alphaPrefixSeries, Finset.prod_range]
  simp [FiniteEdreiData.alphaProduct]

theorem FiniteEdreiData.networkTransfer_eq_psToeplitz_finiteFactor {p q N : ℕ}
    (D : FiniteEdreiData p q) :
    FiniteEdreiData.networkTransfer D N = psToeplitz N D.finiteFactor := by
  rw [FiniteEdreiData.networkTransfer, finiteFactorStageCount,
    FiniteEdreiData.networkFactorPrefix_eq_psToeplitz D (le_refl p),
    FiniteEdreiData.alphaPrefixSeries_eq_alphaProduct D]
  rfl

/-- A trajectory is recursively obtained by adjoining its final vertex. -/
def FiniteFactorWalk {p q : ℕ} (D : FiniteEdreiData p q) (N : ℕ)
    (source : Fin (N + 1)) : (L : ℕ) → Fin (N + 1) → Type
  | 0, sink => PLift (source = sink)
  | L + 1, _ => Σ z : Fin (N + 1), FiniteFactorWalk D N source L z

namespace FiniteFactorWalk

noncomputable instance walkFintype {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} : Fintype (FiniteFactorWalk D N source L sink) := by
  induction L generalizing sink with
  | zero =>
      simp only [FiniteFactorWalk]
      infer_instance
  | succ L ih =>
      simp only [FiniteFactorWalk]
      letI (z : Fin (N + 1)) := ih (sink := z)
      infer_instance

/-- Product of the edge weights of a recursive trajectory. -/
def weight {p q N : ℕ} {D : FiniteEdreiData p q} {source : Fin (N + 1)} :
    {L : ℕ} → {sink : Fin (N + 1)} → FiniteFactorWalk D N source L sink → ℝ
  | 0, _, _ => 1
  | L + 1, sink, W => weight W.2 *
      FiniteEdreiData.networkStepWeight D N L W.1 sink

/-- Recursive edge admissibility. -/
def Valid {p q N : ℕ} {D : FiniteEdreiData p q} {source : Fin (N + 1)} :
    {L : ℕ} → {sink : Fin (N + 1)} → FiniteFactorWalk D N source L sink → Prop
  | 0, _, _ => True
  | L + 1, sink, W => Valid W.2 ∧ NetworkStepAllowed p q N L W.1 sink

noncomputable instance {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (W : FiniteFactorWalk D N source L sink) :
    Decidable (Valid W) := Classical.dec _

/-- The vertex occupied at each level by a recursive trajectory. -/
def position {p q N : ℕ} {D : FiniteEdreiData p q} {source : Fin (N + 1)} :
    {L : ℕ} → {sink : Fin (N + 1)} → FiniteFactorWalk D N source L sink →
      Fin (L + 1) → Fin (N + 1)
  | 0, _, _ => fun _ ↦ source
  | _L + 1, sink, W => Fin.lastCases sink (position W.2)

@[simp]
theorem position_source {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (W : FiniteFactorWalk D N source L sink) :
    position W 0 = source := by
  induction L generalizing sink with
  | zero => rfl
  | succ L ih =>
      change Fin.lastCases sink (position W.2) (0 : Fin (L + 1)).castSucc = source
      rw [Fin.lastCases_castSucc]
      exact ih W.2

@[simp]
theorem position_sink {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (W : FiniteFactorWalk D N source L sink) :
    position W (Fin.last L) = sink := by
  cases L with
  | zero => exact W.down
  | succ L =>
      change Fin.lastCases sink (position W.2) (Fin.last (L + 1)) = sink
      exact Fin.lastCases_last

@[simp]
theorem position_succ_castSucc {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink z : Fin (N + 1)} (W : FiniteFactorWalk D N source L z)
    (i : Fin (L + 1)) :
    FiniteFactorWalk.position (N := N) (D := D) (source := source) (L := L + 1) (sink := sink)
      (⟨z, W⟩ : FiniteFactorWalk D N source (L + 1) sink) i.castSucc = position W i := by
  change Fin.lastCases sink (position W) i.castSucc = position W i
  exact Fin.lastCases_castSucc i

/-- Trajectories with the same endpoints are determined by their vertex functions. -/
theorem position_injective {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} :
    Function.Injective (position : FiniteFactorWalk D N source L sink → _) := by
  induction L generalizing sink with
  | zero =>
      intro W V _
      cases W
      cases V
      rfl
  | succ L ih =>
      rintro ⟨z, W⟩ ⟨u, V⟩ h
      have hzu : z = u := by
        calc
          z = position W (Fin.last L) := (position_sink W).symm
          _ = FiniteFactorWalk.position (D := D) (source := source) (L := L + 1)
              (sink := sink)
              (⟨z, W⟩ : FiniteFactorWalk D N source (L + 1) sink)
              (Fin.last L).castSucc := (position_succ_castSucc W _).symm
          _ = FiniteFactorWalk.position (D := D) (source := source) (L := L + 1)
              (sink := sink)
              (⟨u, V⟩ : FiniteFactorWalk D N source (L + 1) sink)
              (Fin.last L).castSucc := congrFun h _
          _ = position V (Fin.last L) := position_succ_castSucc V _
          _ = u := position_sink V
      subst u
      congr 1
      apply ih
      funext i
      calc
        position W i = FiniteFactorWalk.position (D := D) (source := source) (L := L + 1)
            (sink := sink)
            (⟨z, W⟩ : FiniteFactorWalk D N source (L + 1) sink)
            i.castSucc := (position_succ_castSucc W i).symm
        _ = FiniteFactorWalk.position (D := D) (source := source) (L := L + 1)
            (sink := sink)
            (⟨z, V⟩ : FiniteFactorWalk D N source (L + 1) sink)
            i.castSucc := congrFun h _
        _ = position V i := position_succ_castSucc V i

/-- Recursive validity is exactly edgewise validity of the vertex function. -/
theorem valid_iff {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (W : FiniteFactorWalk D N source L sink) :
    Valid W ↔ ∀ t : Fin L, NetworkStepAllowed p q N t.val
      (position W t.castSucc) (position W t.succ) := by
  induction L generalizing sink with
  | zero => simp [Valid]
  | succ L ih =>
      rcases W with ⟨z, W⟩
      change (Valid W ∧ NetworkStepAllowed p q N L z sink) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hprefix, hlast⟩ t
        refine Fin.lastCases ?_ (fun i ↦ ?_) t
        · simpa [position_succ_castSucc, position_sink] using hlast
        · rw [show i.castSucc.succ = i.succ.castSucc by apply Fin.ext; rfl]
          simpa only [position_succ_castSucc] using hprefix i
      · intro h
        constructor
        · intro i
          have hi := h i.castSucc
          rw [show i.castSucc.succ = i.succ.castSucc by apply Fin.ext; rfl] at hi
          simpa only [position_succ_castSucc] using hi
        · simpa [position_succ_castSucc, position_sink] using h (Fin.last L)

/-- Recursive weight agrees with the product along the vertex function. -/
theorem weight_eq_prod {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (W : FiniteFactorWalk D N source L sink) :
    weight W = ∏ t : Fin L, FiniteEdreiData.networkStepWeight D N t.val
      (position W t.castSucc) (position W t.succ) := by
  induction L generalizing sink with
  | zero => simp [weight]
  | succ L ih =>
      rcases W with ⟨z, W⟩
      rw [weight, Fin.prod_univ_castSucc, ih]
      congr 1
      · apply Fintype.prod_congr
        intro i
        rw [show i.castSucc.succ = i.succ.castSucc by apply Fin.ext; rfl]
        simp only [position_succ_castSucc]
        rw [show i.castSucc.val = i.val by rfl]
      · simp [position_succ_castSucc, position_sink]

/-- Transfer entries are sums of the weights of all recursive trajectories. -/
theorem networkTransferPrefix_apply_eq_sum_walk {p q N : ℕ}
    (D : FiniteEdreiData p q) (L : ℕ) (source sink : Fin (N + 1)) :
    FiniteEdreiData.networkTransferPrefix D N L source sink =
      ∑ W : FiniteFactorWalk D N source L sink, weight W := by
  induction L generalizing sink with
  | zero =>
      by_cases h : source = sink
      · subst sink
        simp [FiniteEdreiData.networkTransferPrefix, FiniteFactorWalk, weight]
      · simp [FiniteEdreiData.networkTransferPrefix, FiniteFactorWalk, weight, h]
  | succ L ih =>
      rw [FiniteEdreiData.networkTransferPrefix, Matrix.mul_apply]
      simp_rw [ih, Finset.sum_mul]
      simp only [FiniteEdreiData.networkStageMatrix, FiniteFactorWalk, weight]
      exact (Fintype.sum_sigma fun W : Σ z : Fin (N + 1),
        FiniteFactorWalk D N source L z ↦
          weight W.2 * FiniteEdreiData.networkStepWeight D N L W.1 sink).symm

end FiniteFactorWalk

theorem FiniteEdreiData.networkStepWeight_eq_zero_of_not_allowed
    {p q N t : ℕ} (D : FiniteEdreiData p q) (x y : Fin (N + 1))
    (hbad : ¬NetworkStepAllowed p q N t x y) :
    FiniteEdreiData.networkStepWeight D N t x y = 0 := by
  unfold NetworkStepAllowed at hbad
  unfold FiniteEdreiData.networkStepWeight
  by_cases hstay : y.val = x.val
  · exact False.elim (hbad (by simp [hstay]))
  · rw [if_neg hstay]
    split <;> rename_i ht
    · have hstep : y.val ≠ x.val + 1 := by
        intro h
        exact hbad (by simp [ht, h])
      simp [hstep]
    · by_cases ha : (t - q) / N < p
      · have hstep : ¬(x.val = (t - q) % N ∧ y.val = x.val + 1) := by
          intro h
          exact hbad (by simp [ht, ha, h])
        simp [ha, hstep]
      · simp [ha]

namespace FiniteFactorWalk

/-- Invalid trajectories have zero weight. -/
theorem weight_eq_zero_of_not_valid {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (W : FiniteFactorWalk D N source L sink)
    (hbad : ¬Valid W) : weight W = 0 := by
  induction L generalizing sink with
  | zero => exact False.elim (hbad trivial)
  | succ L ih =>
      simp only [Valid, not_and_or] at hbad
      rcases hbad with hprefix | hlast
      · simp [weight, ih W.2 hprefix]
      · rw [weight,
          FiniteEdreiData.networkStepWeight_eq_zero_of_not_allowed D _ _ hlast,
          mul_zero]

/-- Build a recursive trajectory from a vertex function with fixed endpoints. -/
def ofPosition {p q N : ℕ} {D : FiniteEdreiData p q} {source : Fin (N + 1)} :
    {L : ℕ} → {sink : Fin (N + 1)} →
      (f : Fin (L + 1) → Fin (N + 1)) → f 0 = source → f (Fin.last L) = sink →
        FiniteFactorWalk D N source L sink
  | 0, _, f, hsource, hsink => by
      exact ⟨calc
          source = f 0 := hsource.symm
          _ = f (Fin.last 0) := by congr
          _ = _ := hsink⟩
  | L + 1, _, f, hsource, _ =>
      ⟨f (Fin.last L).castSucc,
        ofPosition (fun i ↦ f i.castSucc) (by simpa using hsource) rfl⟩

@[simp]
theorem position_ofPosition {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (f : Fin (L + 1) → Fin (N + 1))
    (hsource : f 0 = source) (hsink : f (Fin.last L) = sink) :
    position (ofPosition (D := D) f hsource hsink) = f := by
  induction L generalizing sink with
  | zero =>
      funext i
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact hsource.symm
  | succ L ih =>
      change (fun i ↦ Fin.lastCases sink
        (position (ofPosition (D := D) (fun k ↦ f k.castSucc)
          (by simpa using hsource) rfl)) i) = f
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [Fin.lastCases_last]
        exact hsink.symm
      · rw [Fin.lastCases_castSucc, ih]

theorem valid_ofPosition_iff {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (f : Fin (L + 1) → Fin (N + 1))
    (hsource : f 0 = source) (hsink : f (Fin.last L) = sink) :
    Valid (ofPosition (D := D) f hsource hsink) ↔
      ∀ t : Fin L, NetworkStepAllowed p q N t.val (f t.castSucc) (f t.succ) := by
  rw [valid_iff, position_ofPosition]

/-- The recursive walk encoding is inverse to reading off its vertex function. -/
theorem ofPosition_position {p q N L : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (W : FiniteFactorWalk D N source L sink) :
    ofPosition (D := D) (position W) (position_source W) (position_sink W) = W := by
  apply position_injective
  exact position_ofPosition _ _ _

/-- Valid full trajectories are exactly the network paths. -/
noncomputable def pathEquivValidWalk {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} :
    FiniteFactorPath D N source sink ≃
      {W : FiniteFactorWalk D N source (finiteFactorStageCount p q N) sink // Valid W} where
  toFun P := ⟨ofPosition (D := D) P.position P.source_eq P.sink_eq,
    (valid_ofPosition_iff P.position P.source_eq P.sink_eq).2 P.valid⟩
  invFun W :=
    { position := position W.1
      source_eq := position_source W.1
      sink_eq := position_sink W.1
      valid := (valid_iff W.1).1 W.2 }
  left_inv P := by
    apply FiniteFactorPath.position_injective
    exact position_ofPosition _ _ _
  right_inv W := by
    apply Subtype.ext
    exact ofPosition_position W.1

theorem pathEquivValidWalk_weight {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink) :
    weight (pathEquivValidWalk P).1 = P.weight := by
  change weight (ofPosition (D := D) P.position P.source_eq P.sink_eq) = P.weight
  rw [weight_eq_prod, position_ofPosition]
  exact rfl

/-- The full transfer entry is the sum over valid network paths. -/
theorem networkTransfer_apply_eq_pathSum {p q N : ℕ}
    (D : FiniteEdreiData p q) (source sink : Fin (N + 1)) :
    FiniteEdreiData.networkTransfer D N source sink =
      FiniteFactorPath.pathSum D N source sink := by
  rw [FiniteEdreiData.networkTransfer,
    networkTransferPrefix_apply_eq_sum_walk]
  let good := fun W : FiniteFactorWalk D N source (finiteFactorStageCount p q N) sink ↦ Valid W
  have hsplit := Fintype.sum_subtype_add_sum_subtype good
    (fun W : FiniteFactorWalk D N source (finiteFactorStageCount p q N) sink ↦ weight W)
  rw [← hsplit]
  have hbad :
      (∑ W : {W : FiniteFactorWalk D N source (finiteFactorStageCount p q N) sink //
          ¬good W}, weight W.1) = 0 := by
    apply Finset.sum_eq_zero
    intro W hW
    exact weight_eq_zero_of_not_valid W.1 W.2
  rw [hbad, add_zero]
  unfold FiniteFactorPath.pathSum
  calc
    (∑ W : {W : FiniteFactorWalk D N source (finiteFactorStageCount p q N) sink //
        Valid W}, weight W.1) =
        ∑ P : FiniteFactorPath D N source sink,
          weight (pathEquivValidWalk P).1 :=
      (pathEquivValidWalk.sum_comp (fun W ↦ weight W.1)).symm
    _ = ∑ P : FiniteFactorPath D N source sink, P.weight := by
      apply Fintype.sum_congr
      intro P
      exact pathEquivValidWalk_weight P

end FiniteFactorWalk

/-- Every transfer entry is the corresponding finite-factor coefficient. -/
theorem FiniteEdreiData.networkTransfer_apply_eq_finiteFactorCoefficient
    {p q N : ℕ} (D : FiniteEdreiData p q) (source sink : Fin (N + 1)) :
    FiniteEdreiData.networkTransfer D N source sink =
      if source.val ≤ sink.val then D.finiteFactorCoefficient (sink.val - source.val) else 0 := by
  rw [FiniteEdreiData.networkTransfer_eq_psToeplitz_finiteFactor]
  rfl

/-- Path sums compute finite-factor coefficients on weakly increasing endpoints. -/
theorem FiniteFactorPath.pathSum_eq_finiteFactorCoefficient
    {p q N : ℕ} (D : FiniteEdreiData p q) {source sink : Fin (N + 1)}
    (h : source.val ≤ sink.val) :
    FiniteFactorPath.pathSum D N source sink =
      D.finiteFactorCoefficient (sink.val - source.val) := by
  rw [← FiniteFactorWalk.networkTransfer_apply_eq_pathSum,
    FiniteEdreiData.networkTransfer_apply_eq_finiteFactorCoefficient D,
    if_pos h]

end ToeplitzPositroids.Edrei
