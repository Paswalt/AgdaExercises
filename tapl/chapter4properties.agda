import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

-- Negation
data ⊥ : Set where
  -- empty

¬_ : Set → Set
¬ A = (A → ⊥)

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- First, we define the syntax of our language as in the book
data Term : Set where
  TmTrue   : Term
  TmFalse  : Term
  TmIf     : Term → Term → Term → Term
  TmZero   : Term
  TmSucc   : Term → Term
  TmPred   : Term → Term
  TmIsZero : Term → Term

-- We declare which of the terms are values
data NumericalValue : Term → Set where
  zero  : NumericalValue TmZero
  sucNv : ∀ {t : Term} → NumericalValue t → NumericalValue (TmSucc t)

data Value : Term → Set where
  true       : Value TmTrue
  false      : Value TmFalse
  numericVal : ∀ {t : Term} → NumericalValue t → Value t

-- Now we can translate the operational semantics into a predicate
data _↪_ : Term → Term → Set where
  E-IfTrue     : ∀ {t₂ t₃ : Term} → TmIf TmTrue t₂ t₃ ↪ t₂
  E-IfFalse    : ∀ {t₂ t₃ : Term} → TmIf TmFalse t₂ t₃ ↪ t₃
  E-PredZero   : TmPred TmZero ↪ TmZero
  E-PreddSucc  : ∀ {t : Term} → NumericalValue t → TmPred (TmSucc t) ↪ t 
  E-Pred       : ∀ {t₁ t₁'} → t₁ ↪ t₁' → TmPred t₁ ↪ TmPred t₁'
  E-If         : ∀ {t₁ t₁' t₂ t₃ : Term} → t₁ ↪ t₁' → TmIf t₁ t₂ t₃ ↪ TmIf t₁' t₂ t₃
  E-Succ       : ∀ {t₁ t₁' : Term} → t₁ ↪ t₁' → TmSucc t₁ ↪ TmSucc t₁'
  E-IsZero     : ∀ {t₁ t₁' : Term} → t₁ ↪ t₁' → TmIsZero t₁ ↪ TmIsZero t₁'
  E-IsZeroSucc : ∀ {t₁ : Term} → NumericalValue t₁ → TmIsZero (TmSucc t₁) ↪ TmFalse
  E-IsZeroZero : TmIsZero TmZero ↪ TmTrue
  
-- Now we can for example prove the determinacy property from the book:
lemma : ∀ {t t' : Term} → t ↪ t' → ¬ Value t
lemma (E-Succ t↪t') (numericVal (sucNv x)) = lemma t↪t' (numericVal x)

↪-determinacy : ∀ {t t' t'' : Term} → t ↪ t' → t ↪ t'' → t' ≡ t''
↪-determinacy E-IfTrue E-IfTrue = refl
↪-determinacy E-IfFalse E-IfFalse = refl
↪-determinacy E-PredZero E-PredZero = refl
↪-determinacy (E-PreddSucc x) (E-PreddSucc x₁) = refl
↪-determinacy (E-PreddSucc x) (E-Pred t↪t'') = ⊥-elim (lemma t↪t'' (numericVal (sucNv x)))
↪-determinacy (E-Pred t↪t') (E-PreddSucc x) = ⊥-elim (lemma t↪t' (numericVal (sucNv x)))
↪-determinacy (E-Pred t↪t') (E-Pred t↪t'') = cong TmPred (↪-determinacy t↪t' t↪t'')
↪-determinacy (E-If {t₁} {t₁'} {t₂} {t₃} t↪t') (E-If {t₁} {t₁''} {t₂} {t₃} t↪t'') = cong (λ x → TmIf x t₂ t₃) (↪-determinacy t↪t' t↪t'')
↪-determinacy (E-Succ t↪t') (E-Succ t↪t'') = cong TmSucc (↪-determinacy t↪t' t↪t'')
↪-determinacy (E-IsZero t↪t') (E-IsZero t↪t'') = cong TmIsZero (↪-determinacy t↪t' t↪t'')
↪-determinacy (E-IsZero (E-Succ ())) (E-IsZeroSucc zero)
↪-determinacy (E-IsZero (E-Succ (E-Succ t↪t'))) (E-IsZeroSucc (sucNv x)) = ⊥-elim (lemma t↪t' (numericVal x))
↪-determinacy (E-IsZeroSucc zero) (E-IsZero (E-Succ ()))
↪-determinacy (E-IsZeroSucc (sucNv x)) (E-IsZero (E-Succ (E-Succ t↪t''))) = ⊥-elim (lemma t↪t'' (numericVal x))
↪-determinacy (E-IsZeroSucc x) (E-IsZeroSucc x₁) = refl
↪-determinacy E-IsZeroZero E-IsZeroZero = refl
