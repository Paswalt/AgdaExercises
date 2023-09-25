import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

-- The ∀ {A} quantifier is just syntactic sugar {A : _}
-- universal quantification is modelled by dependent functions

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M


-------------------------------------------------Exercises---------------------------------------

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
   (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀-distrib-× = record { to = λ x → ⟨ (λ x₁ → proj₁ (x x₁)) , (λ x₁ → proj₂ (x x₁)) ⟩
                     ; from = λ x x₁ → ⟨ (proj₁ x) x₁ , (proj₂ x) x₁ ⟩
                     ; from∘to = λ x → refl
                     ; to∘from = λ y → refl
                     } 

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
   (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x

⊎∀-implies-∀⊎ (inj₁ x) a = inj₁ (x a)
⊎∀-implies-∀⊎ (inj₂ y) a = inj₂ (y a)

-- The converse does not hold, as we can not go from a specific instance like B x or C x
-- that holds for some (x : A) to conclude that it holds ∀ (x : A)

-- We need extensionality for dependent functions for the next task

postulate
  d-extensionality : ∀ {A : Set} {B : A → Set} {f g : (∀ ( x : A) → B x)} → ((x : A) → f x ≡ g x) → f ≡ g 

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

tri-iso : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
tri-iso = record { to = λ x → ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩
                 ; from = λ{ x aa → proj₁ x
                 ; x bb → proj₁ (proj₂ x)
                 ; x cc → proj₂ (proj₂ x)}
                 ; from∘to = λ x → d-extensionality λ{ aa → refl ; bb → refl ; cc → refl}
                 ; to∘from = λ y → refl
                 }
