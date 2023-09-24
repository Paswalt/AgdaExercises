open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import isomorphism using (_≃_; extensionality)


-- Negation is the implication of any type to the empty type
¬_ : Set → Set
¬ A = (A → ⊥)

-- Given evidence that both ¬ A and A hold, we can conclude that ⊥ holds.
-- In other words, if both ¬ A and A hold, then we have a contradiction:
¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

-- Precedence
infix 3 ¬_

-- Since Agda uses intuitionistic logic we can have
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  = λ{¬x → ¬x x}

-- but not ¬¬A → A !

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x


¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)


contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)

contraposition A→B ¬B A = ¬B (A→B A)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)


-- Absurd pattern () tells us that there's no evidence of this form
_ : 4 ≢ 5
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()


-- Any two proofs of a negation are equal
-- ⊥-elim was that, given ⊥ we can conclude anything we want
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x' = extensionality λ x → ⊥-elim (¬x x)


-------------------------------------------Exercises--------------------------------------
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}   → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
-- <-irreflexive {zero} () | This is implicitly assumed, hence we can recursively call to absurdum
<-irreflexive {suc n} (s<s n<n) = <-irreflexive n<n
