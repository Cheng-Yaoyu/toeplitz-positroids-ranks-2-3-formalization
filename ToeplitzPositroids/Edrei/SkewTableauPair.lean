import ToeplitzPositroids.Edrei.SkewTableau
import ToeplitzPositroids.Edrei.FormalSeries

/-!
# Supersymmetric skew-tableau pairs

A term in the coproduct expansion consists of an alpha-oriented tableau on the inner skew shape
and a beta-oriented tableau on the complementary outer skew shape.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

/-- A pair of bounded skew tableaux carrying one alpha and one beta monomial. -/
structure SupersymmetricSkewTableauPair
    {ra wa rb wb p q : ℕ}
    (A : FiniteSkewShape ra wa) (B : FiniteSkewShape rb wb) where
  alphaTableau : AlphaSkewTableau A p
  betaTableau : BetaSkewTableau B q

namespace SupersymmetricSkewTableauPair

instance {ra wa rb wb p q : ℕ} {A : FiniteSkewShape ra wa} {B : FiniteSkewShape rb wb} :
    Finite (SupersymmetricSkewTableauPair (p := p) (q := q) A B) := by
  apply Finite.of_injective
    (fun T ↦ (T.alphaTableau, T.betaTableau))
  intro T U h
  have ha : T.alphaTableau = U.alphaTableau := congrArg Prod.fst h
  have hb : T.betaTableau = U.betaTableau := congrArg Prod.snd h
  cases T
  cases U
  cases ha
  cases hb
  rfl

noncomputable instance {ra wa rb wb p q : ℕ}
    {A : FiniteSkewShape ra wa} {B : FiniteSkewShape rb wb} :
    Fintype (SupersymmetricSkewTableauPair (p := p) (q := q) A B) :=
  Fintype.ofFinite _

/-- Product of the alpha and beta monomials of a tableau pair. -/
def weight {ra wa rb wb p q : ℕ}
    {A : FiniteSkewShape ra wa} {B : FiniteSkewShape rb wb}
    (D : FiniteEdreiData p q)
    (T : SupersymmetricSkewTableauPair (p := p) (q := q) A B) : ℝ :=
  T.alphaTableau.weight D.alpha * T.betaTableau.weight D.beta

theorem weight_pos {ra wa rb wb p q : ℕ}
    {A : FiniteSkewShape ra wa} {B : FiniteSkewShape rb wb}
    (D : FiniteEdreiData p q)
    (T : SupersymmetricSkewTableauPair (p := p) (q := q) A B) :
    0 < weight D T :=
  mul_pos (T.alphaTableau.weight_pos D.alpha_pos)
    (T.betaTableau.weight_pos D.beta_pos)

end SupersymmetricSkewTableauPair

end ToeplitzPositroids.Edrei
