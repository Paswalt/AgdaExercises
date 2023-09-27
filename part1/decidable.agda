import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import relations using (_<_; z<s; _≤_; z≤n; s≤s)
open import isomorphism using (_⇔_)


-- We look at the difference between evidence and computation based relations
-- Previously we defined ≤ as an inductive datatype over evidence but
-- we can also model it as a function from naturals to booleans
data 𝔹 : Set where
  true  : 𝔹
  false : 𝔹

_≤ᵇ_ : ℕ → ℕ → 𝔹
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

infix 4 _≤ᵇ_

-- We can prove the following with that
_ : (2 ≤ᵇ 4) ≡ true
_ = refl

_ : (4 ≤ᵇ 2) ≡ false
_ = refl

-- We can now relate computation and evidence with the help of the following function
T : 𝔹 → Set
T true = ⊤
T false = ⊥
-- This means whenever we have a T b, the resulting type is only inhabited if b is true

-- With this we can show that both ≤ᵇ→≤ and ≤ → ≤ᵇ
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n t = z≤n
≤ᵇ→≤ (suc m) n t = {!!}
