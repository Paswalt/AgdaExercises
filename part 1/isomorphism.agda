import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
---------------------------------------------------Preliminaries-------------------------------------------------------
-- Lambda expressions can be written as λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ } for
-- multiple equations or for a single argument λ x → N or λ (x : A) → N
-- both of which are equivalent to λ{ x → N }

-- In the following we make use of function composition
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x  = g (f x)
-- Equivalently
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

-- The converse from cong-app can -not- be proven in Agda but it is
-- proven to be safe to include it as a postulate.
-- This is the first time a postulate
-- is not this dangerous thing users can misuse but also gives something
-- of value

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- With this we can show equality of functions
-- Consider the following alternative definition of addition
_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' suc n = suc (m + n)

-- We can now show
same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m zero rewrite +-comm m zero = refl
same-app m (suc n) rewrite +-comm m (suc n) | +-comm n m = refl

-- And with this, using extensionality
same : _+'_ ≡ _+_
same = extensionality λ x → extensionality λ x₁ → same-app x x₁
-- In words: To show the equality of both functions we need to
-- show that taking an argument x results in the application
-- of both functions to this x to be the same. This is nothing
-- but yet another function equality to be shown but with one
-- argument plugged in, hence we can apply extensionality a
-- second time and now have to show that the functions applied
-- to x and a new second argument are the same which can be
-- done with the help of same-app that we have established
-- prior
---------------------------------------------------Isomorphism---------------------------------------------------------
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

-- Above the definition of a type isomorphism, this is also the first use
-- of a record type. Isomorphism of types is an equivalence relation

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = record { to = λ{x → x} ; from = λ{x → x} ; from∘to = λ x → refl ; to∘from = λ y → refl }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record { to = from A≃B ; from = to A≃B ; from∘to = to∘from A≃B ; to∘from = from∘to A≃B }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = record { to = (to B≃C) ∘ to A≃B
                         ; from = (from A≃B) ∘ from B≃C
                         ; from∘to = λ{x →
                           begin
                             (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
                           ≡⟨⟩
                             (from A≃B (from B≃C (to B≃C (to A≃B x))))
                           ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
                             from A≃B (to A≃B x)
                           ≡⟨ from∘to A≃B x ⟩
                             x
                           ∎}
                         ; to∘from = λ{y →
                           begin
                             (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
                           ≡⟨⟩
                             to B≃C (to A≃B (from A≃B (from B≃C y)))
                           ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
                             to B≃C (from B≃C y)
                           ≡⟨ to∘from B≃C y ⟩
                             y
                           ∎}
                         }
      

{- It is straightforward to support a variant of equational reasoning for isomorphism.
 We essentially copy the previous definition of equality for isomorphism.
 We omit the form that corresponds to _≡⟨⟩_, since trivial isomorphisms arise
 far less often than trivial equalities: -}
 module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
