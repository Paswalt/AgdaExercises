open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂)
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


data Tricho (m n : ℕ) : Set where
  m<n : m < n → ¬ (n < m) →   ¬ (m ≡ n) → Tricho m n
  n<m : n < m → ¬ (m < n) →   ¬ (m ≡ n) → Tricho m n
  m≡n : ¬ (m < n) → ¬ (n < m) → (m ≡ n) → Tricho m n

<-tricho : ∀ (m n : ℕ) → Tricho m n
<-tricho zero zero = m≡n <-irreflexive <-irreflexive refl
<-tricho zero (suc n) = m<n z<s (λ ()) (λ ())
<-tricho (suc m) zero = n<m z<s ((λ ())) (λ ())
<-tricho (suc m) (suc n) with <-tricho m n
...                         | m<n x y z = m<n (s<s x) (λ{ (s<s x₁) → y x₁}) λ{ refl → z refl}
...                         | n<m x y z = n<m ((s<s x)) (λ{ (s<s x₁) → y x₁}) λ{ refl → z refl}
...                         | m≡n x y refl = m≡n (λ { (s<s x₁) → x x₁ }) (λ { (s<s x₁) → y x₁ }) refl


-- This means nothing but (A ⊎ B) → ⊥ ≃ (A → ⊥) × (B → ⊥)
-- This is just the law C^(A+B) = C^A * C^B which we have
-- already proven in the connectives chapter !

weak-demorgan : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
weak-demorgan = record { to = λ{x → (λ x₁ → x (inj₁ x₁)) Data.Product., λ x₁ → x (inj₂ x₁)}
                       ; from = λ{ (fst Data.Product., snd) (inj₁ x₁) → fst x₁ ; (fst Data.Product., snd) (inj₂ y) → snd y}
                       ; from∘to = λ x → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl}
                       ; to∘from = λ y → refl
                       }

-- Do we also have the reverse?
-- Answer: No! The RHS only implies the LHS, therefore we can only find the from function
--weak-demorgan₂ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
--weak-demorgan₂ = record { to = λ{x → {!!}} ; from = λ{ (inj₁ x) (fst Data.Product., snd) → x fst ; (inj₂ y) (fst Data.Product., snd) → y snd} ; from∘to = {!!} ; to∘from = {!!} }

⊎-case : ∀ {A B C : Set} (f : A → C) (g : B → C) → (x : A ⊎ B) → C
⊎-case f g (inj₁ x) = f x
⊎-case f g (inj₂ y) = g y

weak-demorgan→ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
weak-demorgan→ a⊎b axb = ⊎-case (λ{x → x (proj₁ axb)})(λ{x → x (proj₂ axb)}) a⊎b
---------------------------------------------------------------------------------------------------------------------
-- The law of the excluded middle is not proveable in Agda but we can assume it as an axiom:
postulate
  em : ∀ {A : Set} → A ⊎ (¬ A)

-- It is however, irrefutable, that means:
em-irr : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irr = λ x → x (inj₂ (λ x₁ → x (inj₁ x₁)))

----------------------------------------------------Exercises-------------------------------------------------------
{-
Consider the following principles:

    Excluded Middle: A ⊎ ¬ A, for all A
    Double Negation Elimination: ¬ ¬ A → A, for all A
    Peirce’s Law: ((A → B) → A) → A, for all A and B.
    Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
    De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.

Show that each of these implies all the others.
-}

-- Note that each of them is Set₁
excluded_middle = ∀ (A : Set) → A ⊎ ¬ A
dne = ∀ (A : Set) → ¬ ¬ A → A
plaw = ∀ (A B : Set) → ((A → B) → A) → A
iad = ∀ (A B : Set) → (A → B) → ¬ A ⊎ B
dmg = ∀(A B : Set) →  ¬ (¬ A × ¬ B) → A ⊎ B

em→dne : excluded_middle → dne
em→dne em A = λ x → ⊎-case (λ x₁ → x₁) (λ x₁ → ⊥-elim (x x₁)) (em A)

dne→plaw : dne → plaw
dne→plaw dne A B imp = dne A λ ¬a → ¬a (imp λ a → dne B λ x₁ → ¬a a)

plaw→iad : plaw → iad
plaw→iad pl A B A→B = pl (¬ A ⊎ B) ⊥ λ x → inj₁ λ x₁ → x (inj₂ (A→B x₁)) 

iad→dmg : iad → dmg
iad→dmg iad A B ev with (iad A A λ{x → x}) | (iad B B λ{y → y})
...                        | inj₁ a | inj₁ b = ⊥-elim (ev (a Data.Product., b))
...                        | inj₁ a | inj₂ b = inj₂ b
...                        | inj₂ a | inj₁ b = inj₁ a
...                        | inj₂ a | inj₂ b = inj₁ a


dmg→em : dmg → excluded_middle
dmg→em dmg A = dmg A (¬ A) λ{ (fst Data.Product., snd) → snd fst}



Stable : Set → Set
Stable A = ¬ ¬ A → A

-- (1) Show that any negated formula is stable
neg-stable : ∀ {A : Set} → Stable (¬ A)
neg-stable = λ x x₁ → ¬¬¬-elim x x₁

-- (2) Show that the conjunction of two stable
--     formulas is stable
conj-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
conj-stable {A} {B} sa sb = λ x → (sa λ x₁ → x λ x₂ → x₁ (proj₁ x₂)) Data.Product., sb λ x₁ → x λ x₂ → x₁ (proj₂ x₂) 
