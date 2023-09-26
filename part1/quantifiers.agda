import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import isomorphism using (_≃_; _⇔_; extensionality)
open import relations using (_≤_; s≤s; z≤n; +-mono-≤; ≤-refl; ≤-trans; +-monoˡ-≤)
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

----------------------------------------------------------------------------------------------------
-- We formalise existential quantification by declaring a suitable inductive type:

--data Σ (A : Set) (B : A → Set) : Set where
--  ⟨_,_⟩ : (x : A) → B x → Σ A B

record Σ (A : Set) (B : A → Set) : Set where
  constructor
    ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁

-- Simple example use of an existential
--_ : Σ ℕ (λ n → n ≡ zero)
--_ = ⟨ zero , refl ⟩
----------------------------------------------

-- We define a convenient syntax for existentials as follows:

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

-- Simple example use of the new syntax:
--_ : Σ[ n ∈ ℕ ]  n ≡ zero
--_ = ⟨ zero , refl ⟩
----------------------------------------------

-- Products arise as a special case of existentials, where the second component does not depend on a variable drawn from the first component.

-- A common notation for existentials is ∃ (analogous to ∀ for universals).
-- We follow the convention of the Agda standard library, and reserve this
-- notation for the case where the domain of the bound variable is left implicit:

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Simple example use of the new syntax:
_ : ∃[ n ] (n ≡ zero)
_ = ⟨ zero , refl ⟩
---------------------------------------------

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

----------------------------------------Exercises--------------------------------------
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
   ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃-distrib-⊎ = record { to = λ{ ⟨ x , inj₁ x₁ ⟩ → inj₁ ⟨ x , x₁ ⟩ ; ⟨ x , inj₂ y ⟩ → inj₂ ⟨ x , y ⟩}
                     ; from = λ{ (inj₁ ⟨ x , x₁ ⟩) → ⟨ x , (inj₁ x₁) ⟩ ; (inj₂ ⟨ x , x₁ ⟩) → ⟨ x , (inj₂ x₁) ⟩}
                     ; from∘to = λ{ ⟨ x , inj₁ x₁ ⟩ → refl ; ⟨ x , inj₂ y ⟩ → refl}
                     ; to∘from = λ{ (inj₁ ⟨ x , x₁ ⟩) → refl ; (inj₂ ⟨ x , x₁ ⟩) → refl}
                     }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

∃×-implies-×∃ ⟨ x , ⟨ fst , snd ⟩ ⟩ = ⟨ ⟨ x , fst ⟩ , ⟨ x , snd ⟩ ⟩

-- The converse doesn't hold, because the x must not be the same!
-- Example: There exists x such that x ≡ 0
--          There exists x such that x ≡ 1
--          Since x must be the singular
--          witness of the product, we
--          would require x ≡ 0 and
--          x ≡ 1 to hold, which obviously
--          doesn't work out!

tri∃ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
tri∃ = record { to = λ{ ⟨ aa , x₁ ⟩ → inj₁ x₁ ; ⟨ bb , x₁ ⟩ → inj₂ (inj₁ x₁) ; ⟨ cc , x₁ ⟩ → inj₂ (inj₂ x₁)}
              ; from = λ{ (inj₁ x) → ⟨ aa , x ⟩ ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩ ; (inj₂ (inj₂ y)) → ⟨ cc , y ⟩}
              ; from∘to = λ{ ⟨ aa , x₁ ⟩ → refl ; ⟨ bb , x₁ ⟩ → refl ; ⟨ cc , x₁ ⟩ → refl}
              ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
              }

------------------------------------------------Exercises---------------------------------------------------
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-odd  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
   odd-even : ∀ {n : ℕ} → even n → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-odd on) with odd-∃ on
... | ⟨ m , 1+m*2≡n ⟩ = ⟨ suc m , Eq.cong suc 1+m*2≡n ⟩

odd-∃ (odd-even en) with even-∃ en
... | ⟨ m , m*2≡n ⟩ = ⟨ m , Eq.cong suc m*2≡n ⟩

-- Reverse direction
∃-even : ∀{n : ℕ} → ∃[ m ] (m * 2 ≡ n)     → even n
∃-odd  : ∀{n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → odd  n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-odd (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ zero , refl ⟩ = odd-even even-zero
∃-odd ⟨ suc m , refl ⟩ = odd-even (∃-even ⟨ suc m , refl ⟩)

-----------------------------------------------------------------------------------------
-- Lemmas for the following exercise
+-suceq : ∀ (x y z : ℕ) → x + y ≡ z → x + suc y ≡ suc z
+-suceq zero y .y refl = refl
+-suceq (suc x) y .(suc (x + y)) refl rewrite +-comm x (suc y) | +-comm y x = refl
-----------------------------------------------------------------------------------------

∃-+-≤ : ∀ (y z : ℕ) → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤ zero z ev = z≤n
∃-+-≤ (suc y) .(x + suc y) ⟨ x , refl ⟩ = +-mono-≤ 0 x (suc y) (suc y) z≤n ≤-refl

≤-+-∃ : ∀ (y z : ℕ) → y ≤ z → ∃[ x ] (x + y ≡ z)
≤-+-∃ .0 zero z≤n = ⟨ zero , refl ⟩
≤-+-∃ zero (suc z) ev rewrite +-comm zero z = ⟨ suc z , refl ⟩
≤-+-∃ (suc y) (suc z) (s≤s ev) with ≤-+-∃ y z ev
... | ⟨ x , x₁ ⟩ = ⟨ x , +-suceq x y z x₁ ⟩

-----------------------------------------------------------------------------------------

-- The qunatification rules from logic class also work here of course
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }


∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)

∃¬-implies-¬∀ ⟨ x , x₁ ⟩ = λ x₂ → x₁ (x₂ x)


-----------------------------------------Stretch Exercise-----------------------------------
-- This is copied from the relations chapter:
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 0 + 2 * (from x)
from (x I) = 1 + 2 * (from x)

shift : ∀ (b : Bin) → (from b) + (from b) ≡ (from (b O))
shift ⟨⟩ = refl
shift (b O) rewrite +-comm (from b + (from b + zero)) zero = refl
shift (b I) rewrite +-comm (suc (from b + (from b + 0))) zero = refl

-- We can now define the predicates
data One : Bin → Set where
  singleI : One (⟨⟩ I)
  oneO : ∀ (b : Bin) → One b → One (b O)
  oneI : ∀ (b : Bin) → One b → One (b I)

data Can : Bin → Set where
  canZero : Can (⟨⟩ O)
  canOne  : ∀ (b : Bin) → One b → Can b

-- Now we can do proofs with these predicates
----------------------------------------------------------------------------------------
one-rev-O : ∀ {b : Bin} → One (b O) → One b
one-rev-O (oneO _ ob) = ob

inc-preserve-one : ∀ (b : Bin) → One b → One (inc b)
inc-preserve-one .(⟨⟩ I) singleI = oneO ((⟨⟩ I)) singleI
inc-preserve-one .(b O) (oneO b ob) = oneI b ob
inc-preserve-one .(b I) (oneI b ob) = oneO (inc b) (inc-preserve-one b ob)

can-inc : ∀ {b : Bin} → Can b → Can (inc b)
can-inc canZero = canOne (⟨⟩ I) singleI
can-inc (canOne (b O) x) = canOne ((b I)) (oneI b (one-rev-O x))
can-inc (canOne (b I) x) = canOne ((inc b) O) (inc-preserve-one (b I) x)
----------------------------------------------------------------------------------------
can-to : ∀ (n : ℕ) → Can (to n)
can-to zero = canZero
can-to (suc n) = can-inc (can-to n)
----------------------------------------------------------------------------------------
atleastOne : ∀ (b : Bin) → One b → 1 ≤ from b
atleastOne .(⟨⟩ I) singleI = s≤s z≤n
atleastOne .(b O) (oneO b ob) rewrite +-comm (from b) zero = ≤-trans (atleastOne b ob) (+-monoˡ-≤ 0 ((from b)) ( (from b)) z≤n)
atleastOne .(b I) (oneI b ob) = s≤s z≤n

lshiftnat : ∀ (n : ℕ) → to (2 * (suc n)) ≡ (to (suc n)) O
lshiftnat zero = refl
lshiftnat (suc n) = 
  begin
    to (2 * suc (suc n))
  ≡⟨ cong to (*-comm 2 (suc(suc n)))⟩
    to (suc (suc n) * 2)
  ≡⟨⟩
    to (2 + (suc n * 2))
  ≡⟨⟩
    inc (inc (to (suc n * 2)))
  ≡⟨ cong inc (cong inc (cong to (*-comm (suc n) 2))) ⟩
    inc (inc (to (2 * suc n)))
  ≡⟨ cong inc (cong inc (lshiftnat n)) ⟩
    inc (inc ((to (suc n)) O))
  ≡⟨⟩
    refl


lshift : ∀ (n : ℕ) → 1 ≤ n → to (2 * n) ≡ (to n) O
lshift (suc n) (s≤s 1≤n) = lshiftnat n

can-to-id-one : ∀ (b : Bin) → One b → to (from b) ≡ b
can-to-id-one .(⟨⟩ I) singleI = refl
can-to-id-one .(b O) (oneO b ob) =
  begin
    to (from (b O))
  ≡⟨⟩
    to (2 * from b)
  ≡⟨ lshift (from b) (atleastOne b ob) ⟩
    (to (from b)) O
  ≡⟨ cong (_O) (can-to-id-one b ob) ⟩
    b O
  ∎
  
can-to-id-one .(b I) (oneI b ob) =
  begin
    to (from (b I))
  ≡⟨⟩
    to (1 + 2 * from b)
  ≡⟨⟩
    inc (to (2 * from b))
  ≡⟨ cong inc (lshift (from b) (atleastOne b ob)) ⟩
    inc ( (to (from b)) O)
  ≡⟨⟩
    to (from b) I
  ≡⟨ cong (_I) (can-to-id-one b ob) ⟩
    b I
  ∎

can-to-id : ∀ (b : Bin) → Can b →  to (from b) ≡ b
can-to-id .(⟨⟩ O) canZero = refl
can-to-id b (canOne .b x) = can-to-id-one b x

-- The exercise proposes to use the following lemmas
≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One singleI singleI = refl
≡One (oneO b o) (oneO .b o') = cong (oneO b) (≡One o o')
≡One (oneI b o) (oneI .b o') = cong (oneI b) (≡One o o')

≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
≡Can canZero canZero = refl
≡Can canZero (canOne .(⟨⟩ O) (oneO .⟨⟩ ()))
≡Can (canOne _ (oneO .⟨⟩ ())) canZero
≡Can (canOne b x) (canOne b x₁) = cong (canOne b ) (≡One x x₁)

proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → Σ.proj₁ cb ≡ Σ.proj₁ cb′ → cb ≡ cb′
proj₁≡→Can≡ {⟨ .(⟨⟩ O) , canZero ⟩} {⟨ .(⟨⟩ O) , canZero ⟩} refl = refl
proj₁≡→Can≡ {⟨ .(⟨⟩ O) , canOne .(⟨⟩ O) (oneO .⟨⟩ ()) ⟩} {⟨ .(⟨⟩ O) , canZero ⟩} refl
proj₁≡→Can≡ {⟨ .(⟨⟩ O) , canZero ⟩} {⟨ .(⟨⟩ O) , canOne .(⟨⟩ O) (oneO .⟨⟩ ()) ⟩} refl
proj₁≡→Can≡ {⟨ .proj₄ , canOne .proj₄ x₁ ⟩} {⟨ proj₄ , canOne .proj₄ x ⟩} refl rewrite (≡Can (canOne proj₄ x₁) (canOne proj₄ x)) = refl

+neutral : ∀ (n : ℕ) → n + zero ≡ n
+neutral zero = refl
+neutral (suc n) rewrite +-comm n zero = refl

increment : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
increment ⟨⟩ = refl
increment (b O) = refl
increment (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    2 * (from (inc b))
  ≡⟨ cong (2 *_) (increment b) ⟩
    2 * suc (from b)
  ≡⟨⟩
    suc (from b) + 1 * suc (from b)
  ≡⟨⟩
    suc (from b) + (suc (from b) + 0)
  ≡⟨ cong ((suc (from b)) +_) (+neutral (suc (from b))) ⟩
    suc (from b) + suc (from b)
  ≡⟨⟩
    suc ((from b) + suc (from b))
  ≡⟨ cong suc (+-comm (from b) (suc (from b))) ⟩
    suc(suc((from b) + (from b)))
  ≡⟨ cong suc (cong suc (shift b)) ⟩
    suc(suc(from (b O)))
  ≡⟨⟩
    refl


-- The second law doesn't hold. This follows because e.g.
-- the bit strings ⟨⟩ O O I and ⟨⟩ I both convert to 1
-- but the function can only convert the natural 1 back
-- to one of these bit strings (in this case ⟨⟩ I) so
-- giving the first bitstring as input would be a
-- counterexample

-- The third law holds. Proof:

from-to : ∀ n → from (to n) ≡ n
from-to zero = refl
from-to (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ increment (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from-to n) ⟩
    suc n
  ∎

-- Now onto the isomorphism
iso : ℕ ≃ ∃[ b ] Can b
iso = record { to = λ{n → ⟨ to n , can-to n ⟩}
             ; from = λ{ ⟨ b , cb ⟩ → from b}
             ; from∘to  = λ{ zero → refl ; (suc n) → 
             begin
               from (to ( suc n))
             ≡⟨ from-to (suc n) ⟩
               suc n
             ∎
             }
             --to(from(b))
             ; to∘from = λ{ ⟨ b , cb ⟩ → proj₁≡→Can≡ (
               begin
                 to( from b )
               ≡⟨ can-to-id b cb ⟩
                 b
               ∎)
               } 
             }
