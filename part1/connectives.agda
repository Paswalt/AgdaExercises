-- Based on the propositions as types correspondence, we can find
-- connections between logcal connectives and different types.
-- In fact, we have that:

-- conjunction ∧ = product ×
-- disjunction ∨ = sum     ⨃
-- true          = unit   ( )
-- false         = empty   ⊥
-- implication → = function space

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open isomorphism.≃-Reasoning

-- (1) Conjunction is product
data _×_ (A B : Set) : Set where
  ⟨_,_⟩ :
          A
        → B
        -------
        → A × B

-- Given evidence that A × B we can conclude A and B individually
proj₁ : ∀ {A B : Set}
      → A × B
      -------
      → A

proj₁ ⟨ x , x₁ ⟩ = x

proj₂ : ∀ {A B : Set}
      → A × B
      -------
      → B

proj₂ ⟨ x , x₁ ⟩ = x₁

-- This is already defined when using records for × like the standard
-- library does. However, for now we will use the ⟨_,_⟩ notion
η-× : ∀ {A B : Set} → (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , x₁ ⟩ = refl

-- Precedence
infixr 2 _×_

-- Product is commutative up to isomorphism
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record { to = λ{w → ⟨ proj₂ w , proj₁ w ⟩}
                ; from = λ{w → ⟨ proj₂ w , proj₁ w ⟩}
                ; from∘to = λ{ ⟨ x , x₁ ⟩ → refl}
                ; to∘from = λ{ ⟨ x , x₁ ⟩ → refl}
                }

-- Product is associative up to isomorphism
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record { to = λ{w → ⟨ proj₁ (proj₁ w) , ⟨ proj₂ (proj₁ w) , proj₂ w ⟩ ⟩}
                 ; from = λ{w → ⟨ ⟨ proj₁ w , proj₁ (proj₂ w) ⟩ , proj₂ (proj₂ w)⟩}
                 ; from∘to = λ{ ⟨ ⟨ x₁ , x₂ ⟩ , x ⟩ → refl}
                 ; to∘from = λ{ ⟨ x , ⟨ x₁ , x₂ ⟩ ⟩ → refl}
                 }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record { to = λ{w → ⟨ _⇔_.to w , _⇔_.from w ⟩}
             ; from = λ{w → record { to = proj₁ w ; from = proj₂ w }}
             ; from∘to = λ{ record { to = to ; from = from } → refl}
             ; to∘from = λ{ ⟨ x , x₁ ⟩ → refl}
             }

-- (2) Truth is unit
data ⊤ : Set where
  tt :
     -----
     ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

-- The unit type is the identity for product (up to isomorphism)
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎


-- (3) Disjunction is sum
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

-- More generally, we can also throw in an arbitrary function from a disjunction:
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

-- Precedence
infixr 1 _⊎_

-- Sum is also commutative and associative up to isomorphism

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record { to = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x}
                ; from = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x}
                ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ x) → refl}
                ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ x) → refl}
                }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record { to = λ{ (inj₁ (inj₁ x)) → inj₁ x ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x) ; (inj₂ x) → inj₂ (inj₂ x)}
                 ; from = λ{ (inj₁ x) → inj₁ (inj₁ x) ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x) ; (inj₂ (inj₂ x)) → inj₂ x}
                 ; from∘to = λ{ (inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ x)) → refl ; (inj₂ x) → refl}
                 ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ x)) → refl}
                 }


-- (4) False is empty
data ⊥ : Set where
  -- No clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

-- This is our first use of the absurd pattern (). Here since ⊥ is a type with no members,
-- we indicate that it is never possible to match against a value of this type by using the
-- pattern ()
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

-- The empty type is the identity of sums up to isomorphism

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ = record { to = λ{ (inj₁ x) → x} ; from = λ{w → inj₁ w} ; from∘to = λ{ (inj₁ x) → refl} ; to∘from = λ{w → refl} }

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ {A} =
  ≃-begin
    (⊥ ⊎ A)
  ≃⟨ ⊎-comm ⟩
    ((A ⊎ ⊥))
  ≃⟨ ⊥-identityʳ ⟩
    A
  ≃-∎


-- (5) Implication is function
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

-- ̂| Modus ponens ̂|
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

-- The function space (A → B) is also called exponential. This is
-- because of |A| = m and |B| = n we have n^m elements inhabiting (A → B)
-- Exponential on types also share many similarities with naturals

-- LHS: (|C|^|B|)^|A| and RHS: |C|^(|A| * |B|)
-- Corresponding to (p ^ n) ^ m  ≡  p ^ (n * m)
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- Corresponding to p ^ (n + m) = (p ^ n) * (p ^ m)
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

-- Corresponding (p * n) ^ m = (p ^ m) * (n ^ m)
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }


-- Products distribute over sum, up to isomorphism.

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

-- Sums do not distribute over products up to isomorphism, but it is an embedding:
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }


---------------------------------------Exercises-----------------------------------
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , x₁ ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , x₁ ⟩ = inj₂ (⟨ x , x₁ ⟩)

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , x₁ ⟩) = ⟨ inj₁ x , inj₁ x₁ ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , x₁ ⟩) = ⟨ inj₂ x , inj₂ x₁ ⟩
-- Does the converse hold?

-- Counterexample
-- Claim: ⊭ (A ∨ B) ∧ (C ∨ D) → (A ∧ B) ∨ (C ∧ D)
-- Choose
-- A → 1
-- B → 0
-- C → 1
-- D → 0
