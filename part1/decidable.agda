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
open import relations using (_<_; z<s; s<s; _≤_; z≤n; s≤s)
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
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ (m n : ℕ) → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ zero n m≤n = tt
≤→≤ᵇ (suc m) (suc n) (s≤s m≤n) = ≤→≤ᵇ m n m≤n

--------------------------------------------Decidable----------------------------------
-- The issue with booleans is that other than evidence, there is nothing we can inspect
-- and therefore nothing we can gain from a single bit of information, from a simple
-- true or false. We can combine the best of both worlds, having a true false statement
-- and evidence that we can observe if we should want to by defining a suitable new
-- datatype: decidable

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

-- It is straightforward to decide inequality. The convention when deciding something is
-- to use a question mark in its name

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no λ{ ()}
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no  m≰n = no λ{ (s≤s m≤n) → m≰n m≤n}

--------------------------------------Exercises------------------------------------------
_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no λ{ ()}
zero <? suc n = yes z<s
suc m <? zero = no λ{ ()}
suc m <? suc n with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no  m≮n = no λ{ (s<s m<n) → m≮n m<n}

_≡ℕ_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ zero = yes refl
zero ≡ℕ suc n = no λ{ ()}
suc m ≡ℕ zero = no λ{ ()}
suc m ≡ℕ suc n with m ≡ℕ n
...               | yes refl = yes refl
...               | no  m≢n = no λ{ refl → m≢n refl}
-----------------------------------------------------------------------------------------

-- Erasure takes a decidable value to a boolean
-- this means we 'erase' the evidence and just
-- extract the single bit of information
⌊_⌋ : ∀ {A : Set} → Dec A → 𝔹
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false


-- Using erasure, we can easily derive _≤ᵇ_ from _≤?_:
_≤ᵇ′_ : ℕ → ℕ → 𝔹
m ≤ᵇ′ n = ⌊ m ≤? n ⌋


-- Further, if D is a value of type Dec A, then T ⌊ D ⌋ is inhabited exactly when A is inhabited:

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

-- Using these, we can easily derive that T (m ≤ᵇ′ n) is inhabited exactly when m ≤ n is inhabited:

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

-- In summary, it is usually best to eschew booleans and rely on decidables.
-- If you need booleans, they and their properties are easily derived from the corresponding decidables.

-------------------------------------------Connectives--------------------------------------------------
-- Decidiability for connectives is equivalent to decidabality for booleans
infixr 6 _∧_

_∧_ : 𝔹 → 𝔹 → 𝔹
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes x₁ = yes ⟨ x , x₁ ⟩
_  ×-dec no x₁ = no λ{ ⟨ fst , snd ⟩ → x₁ snd}
no x ×-dec _ = no λ{ ⟨ fst , snd ⟩ → x fst}

infixr 5 _∨_

_∨_ : 𝔹 → 𝔹 → 𝔹
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _ = yes (inj₁ x)
_ ⊎-dec yes x₁ = yes (inj₂ x₁)
no a ⊎-dec no b = no λ{ (inj₁ x) → a x ; (inj₂ y) → b y}

not : 𝔹 → 𝔹
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no λ x₁ → x₁ x
¬? (no x) = yes x

_⊃_ : 𝔹 → 𝔹 → 𝔹
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_ →-dec yes x  = yes λ x₂ → x
no x →-dec _ = yes λ x₂ → ⊥-elim (x x₂)
yes x →-dec no y = no λ x₁ → y (x₁ x)

---------------------------------------------------------------------------------
∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋

-- These proof are basically nothing but matching over
-- the decidable evidence, as everything already simplifies
-- nicely thanks to the short-circuit definitions of the connectors
∧-× (yes x) (yes x₁) = refl
∧-× (yes x) (no x₁) = refl
∧-× (no x) (yes x₁) = refl
∧-× (no x) (no x₁) = refl

∨-⊎ (yes x) db = refl
∨-⊎ (no x) (yes x₁) = refl
∨-⊎ (no x) (no x₁) = refl

not-¬ (yes x) = refl
not-¬ (no x) = refl

---------------------------------------------------------------------------------
_iff_ : 𝔹 → 𝔹 → 𝔹
false iff false = true
false iff true  = false
true  iff false = false
true  iff true  = true

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes x₁ = yes (record { to = λ x₂ → x₁ ; from = λ x₂ → x })
yes x ⇔-dec no x₁ = no λ{ record { to = to ; from = from } → x₁ (to x)}
no x ⇔-dec yes x₁ = no λ{ record { to = to ; from = from } → x (from x₁)}
no x ⇔-dec no x₁ = yes (record { to = λ x₂ → ⊥-elim (x x₂) ; from = λ x₂ → ⊥-elim (x₁ x₂) })

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes x) (yes x₁) = refl
iff-⇔ (yes x) (no x₁) = refl
iff-⇔ (no x) (yes x₁) = refl
iff-⇔ (no x) (no x₁) = refl
--------------------------Proof by reflection------------------------------------
minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m


-- The implicit here is a super neat trick that works as a kind
-- of guard that is checked at type-checking time. The trick works
-- because Agda will fill in an implicit of a record type if it can
-- fill in all its fields. That's why T is defined as an empty record
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

-- This works because the implicit is evaluated as T true which is ⊤
_ : 5 - 2 ≡ 3
_ = refl

-- 3 - 5 for instance will throw an error

-- Exercises
toWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ T ⌊ D ⌋ → ¬ A

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → ¬ T ⌊ D ⌋
