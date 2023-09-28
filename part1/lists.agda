import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-comm; +-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import isomorphism using (_≃_; _⇔_; extensionality)
open import connectives using (_⊎_; inj₁; inj₂)

-- List definition in haskell: data List a = Nil | Cons a (List a)
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}



-- We can use pattern to show convenient forms
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []



-- Some list functions
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

-- We can reason about lists in much the same way that we reason about numbers.
-- Here is the proof that append is associative:

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

-- It is also easy to show that [] is a left and right identity for _++_.
-- That it is a left identity is immediate from the definition:

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

-- That it is a right identity follows by simple induction:

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

-- As we will see later, these three properties establish
-- that _++_ and [] form a monoid over lists.
length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc(length xs)

-- The length of one list appended to
-- another is the sum of the lengths of the lists:

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎



reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ lst) = (reverse lst) ++ [ x ]


-------------Exercises------------------------------
reverse-++-distrib : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x ∷ xs) ys rewrite reverse-++-distrib xs ys | ++-assoc (reverse ys) (reverse xs) ([ x ]) = refl

rev-id : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
rev-id [] = refl
rev-id (x ∷ xs) rewrite reverse-++-distrib (reverse xs) ([ x ]) | rev-id xs = refl
-----------------------------------------------------
reverseHelper : ∀ {A : Set} → List A → List A → List A
reverseHelper [] ys = ys
reverseHelper (x ∷ xs) ys = reverseHelper xs ((x ∷ ys))


reverse' : ∀ {A : Set} → List A → List A
reverse' xs = reverseHelper xs []
  where 

rev'-lemma : ∀ {A : Set} (xs ys : List A) → reverseHelper xs ys ≡ reverse xs ++ ys
rev'-lemma [] ys = refl
rev'-lemma (x ∷ xs) ys rewrite rev'-lemma xs (x ∷ ys) | ++-assoc (reverse xs) ([ x ]) (ys) = refl

rev≡rev' : ∀ {A : Set} (xs : List A) → reverse xs ≡ reverse' xs
rev≡rev' [] = refl
rev≡rev' (x ∷ xs) rewrite rev'-lemma xs [ x ] = refl

------------------------------------------------------------------------------------------------------

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

same-map : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
same-map f g [] = refl
same-map f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong ( ((g ∘ f) x) ∷_) (same-map f g xs) ⟩
    g (f x) ∷ (map g ∘ map f) xs
  ≡⟨⟩
    refl

map-comp : ∀ {A B C : Set} (f : A → B) (g : B → C) → map (g ∘ f) ≡ (map g) ∘ (map f) 
map-comp f g = extensionality λ x → same-map f g x

map-++-distrib : ∀ {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distrib f [] ys = refl
map-++-distrib f (x ∷ xs) ys rewrite map-++-distrib f xs ys = refl

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node tree x tree₁) = node (map-Tree f g tree) (g x) (map-Tree f g tree₁)

------------------------------------------------------------------------------------------------------
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

list_prod : List ℕ → ℕ
list_prod xs = foldr _*_ 1 xs

myList : List ℕ
myList = [ 1 , 2 , 3 , 4 ]

myNum : list_prod myList ≡ 24
myNum = refl

fold-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (xs ys : List A) (e : B) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
fold-++ _⊗_ [] ys e = refl
fold-++ _⊗_ (x ∷ xs) ys e rewrite fold-++ _⊗_ xs ys e = refl
-- x ⊗ foldr _⊗_ e (xs ++ ys))

fold-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
fold-∷ [] = refl
fold-∷ (x ∷ xs) rewrite fold-∷ xs = refl

fold-++-∷ : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
fold-++-∷ [] ys = refl
fold-++-∷ (x ∷ xs) ys rewrite fold-++-∷ xs ys = refl

sameMapFold : ∀ {A B : Set} (f : A → B) (xs : List A) → map f xs ≡ foldr (λ y ys → f y ∷ ys) [] xs
sameMapFold f [] = refl
sameMapFold f (x ∷ xs) rewrite sameMapFold f xs = refl

mapIsFold : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
mapIsFold f = extensionality (sameMapFold f)

-- Remember the tree datatype from earlier
--data Tree (A B : Set) : Set where
--  leaf : A → Tree A B
--  node : Tree A B → B → Tree A B → Tree A B
--
-- With the function:
-- map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
-- map-Tree f g (leaf x) = leaf (f x)
-- map-Tree f g (node tree x tree₁) = node (map-Tree f g tree) (g x) (map-Tree f g tree₁)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node tree x tree₁) = g (fold-Tree f g tree) x (fold-Tree f g tree₁)

mapTreeisFoldTree : ∀ {A B C D : Set} (f : A → C) (g : B → D) (t : Tree A B) → map-Tree f g t ≡ fold-Tree (λ a → leaf (f a)) (λ tl b tr → node tl (g b) tr) t
mapTreeisFoldTree f g (leaf x) = refl
mapTreeisFoldTree f g (node t x t₁) rewrite mapTreeisFoldTree f g t | mapTreeisFoldTree f g t₁ = refl

mapTree≡FoldTree : ∀ {A B C D : Set} (f : A → C) (g : B → D) → map-Tree f g ≡ fold-Tree (λ a → leaf (f a)) (λ tl b tr → node tl (g b) tr)
mapTree≡FoldTree f g = extensionality (mapTreeisFoldTree f g)

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n


sum : List ℕ → ℕ
sum = foldr _+_ 0

sum-lemma : ∀ (n : ℕ) → sum (n ∷ downFrom n) ≡ n + sum (downFrom n)
sum-lemma zero = refl
sum-lemma (suc n) rewrite (sym (sum-lemma n)) = refl

*-lemma : ∀ (n : ℕ) → n + n * (n ∸ 1) ≡ n * n
*-lemma zero = refl
*-lemma (suc n) rewrite *-comm n (suc n) = refl

gauss : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
gauss zero = refl
gauss (suc n)  =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    (sum (n ∷ downFrom n)) * 2
  ≡⟨ cong (_* 2) (sum-lemma n) ⟩
    (n + (sum (downFrom n))) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    (n * 2) + ((sum (downFrom n)) * 2)
  ≡⟨ cong ((n * 2) +_) (gauss n) ⟩
    n * 2 + (n * (n ∸ 1))
  ≡⟨ cong (_+ n * (n ∸ 1)) (*-comm n 2) ⟩
    2 * n + n * (n ∸ 1)
  ≡⟨⟩
    n + (n + zero) + n * (n ∸ 1)
  ≡⟨ cong (_+ (n * (n ∸ 1))) (cong (n +_) (+-comm n zero))  ⟩
    n + (zero + n) + n * (n ∸ 1)
  ≡⟨⟩
    n + n + n * (n ∸ 1)
  ≡⟨ +-assoc n n (n * (n ∸ 1)) ⟩
    n + (n + n * (n ∸ 1))
  ≡⟨ cong (n +_) (*-lemma n) ⟩
    n + n * n
  ∎
----------------------------------------------Monoids-------------------------------------------------

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

postulate
  foldr-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

foldl : ∀ {A B : Set} → (_⊗_ : B → A → B) (e : B) (xs : List A) → B 
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (x e : A) (xs : List A) → IsMonoid _⊗_ e → foldl _⊗_ x xs ≡ x ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ x e [] mono rewrite identityʳ mono x = refl
foldl-monoid _⊗_ x e (x₁ ∷ xs) mono rewrite (identityˡ mono x₁) =
  begin
    foldl _⊗_ x (x₁ ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (x ⊗ x₁) xs
  ≡⟨ foldl-monoid _⊗_ (x ⊗ x₁) e xs mono ⟩
    ((x ⊗ x₁) ⊗ foldl _⊗_ e xs)
  ≡⟨ (assoc mono) x x₁ (foldl _⊗_ e xs) ⟩
    (x ⊗ (x₁ ⊗ (foldl _⊗_ e xs)))
  ≡⟨ cong (x ⊗_) (sym (foldl-monoid _⊗_ x₁ e xs mono)) ⟩
    (x ⊗ foldl _⊗_ x₁ xs)
  ≡⟨⟩
    refl
    
foldEqMon : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs : List A) → IsMonoid _⊗_ e → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldEqMon _⊗_ e [] mono = refl
foldEqMon _⊗_ e (x ∷ xs) mono rewrite foldEqMon _⊗_ e xs mono | (identityˡ mono x) | sym (foldl-monoid _⊗_ x e xs mono) = refl

monfold≡ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e → foldr _⊗_ e ≡ foldl _⊗_ e
monfold≡ _⊗_ e mono = extensionality λ x → foldEqMon _⊗_ e x mono

-----------------------------------All and Any---------------------------------------------------------------------------
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩


toAny : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
toAny [] ys anyp = inj₂ anyp
toAny (x ∷ xs) ys (here x₁) = inj₁ (here x₁)
toAny (x ∷ xs) ys (there anyp) with toAny xs ys anyp
...                               | inj₁ y = inj₁ (there y)
...                               | inj₂ z = inj₂ z

fromAny : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    Any P xs ⊎ Any P ys → Any P (xs ++ ys)

fromAny (x₁ ∷ xs) ys (inj₁ (here x)) = here x
fromAny (x₁ ∷ xs) ys (inj₁ (there x)) = there (fromAny xs ys (inj₁ x))
fromAny [] (x₁ ∷ ys) (inj₂ (here x)) = here x
fromAny (x₂ ∷ xs) (x₁ ∷ ys) (inj₂ (here x)) = there (fromAny xs ((x₁ ∷ ys)) (inj₂ (here x)))
fromAny [] (x₁ ∷ ys) (inj₂ (there x)) = there x
fromAny (x₂ ∷ xs) (x₁ ∷ ys) (inj₂ (there x)) = there (fromAny xs ((x₁ ∷ ys)) (inj₂ (there x)))

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)

Any-++-⇔ xs ys = record { to = λ{x → toAny xs ys x}
                        ;from = fromAny xs ys
                        }


toAnyNeg : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
toAnyNeg [] notAny = []
toAnyNeg (x ∷ xs) notAny = (λ x₁ → notAny (here x₁)) ∷ toAnyNeg xs λ x₁ → notAny (there x₁)

fromAnyNeg : ∀ {A : Set} {P : A → Set} (xs : List A) → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
fromAnyNeg [] allNeg = λ{ ()}
fromAnyNeg (x ∷ xs) (x₁ ∷ allNeg) = λ{ (here x) → x₁ x ; (there x₂) → fromAnyNeg xs allNeg x₂}

deMorgan : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
deMorgan xs = record { to = toAnyNeg xs
                     ; from = fromAnyNeg xs
                     }
                     
-- Do we also have the following?
-- (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
-- If so, prove; if not, explain why.

-- ¬ (Any P xs)    ⇔    All (¬P) xs | Does work out
--    Any (¬P) xs  ⇔ ¬ (All P xs)   | Does not work out because for the empty list case we can not find an element to prove Any for example

all-to : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs → (∀ x → (x ∈ xs → P x))
all-to [] allp = λ{ x ()}
all-to (x ∷ xs) (x₁ ∷ allp) = λ{ x₂ (here refl) → x₁ ; x₂ (there x₃) → all-to xs allp x₂ x₃}

all-from : ∀ {A : Set} {P : A → Set} (xs : List A) → (∀ x → (x ∈ xs → P x)) → All P xs
all-from [] f = []
all-from (x ∷ xs) f = f x (here refl) ∷ all-from xs λ x₁ x₂ → f x₁ (there x₂)

all-∀-from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (Pxs : All P xs) → all-from xs (all-to xs Pxs) ≡ Pxs
all-∀-from∘to [] [] = refl
all-∀-from∘to (x ∷ xs) (x₁ ∷ Pxs) =
  begin
    all-from (x ∷ xs) (all-to (x ∷ xs) (x₁ ∷ Pxs))
  ≡⟨⟩
    x₁ ∷ all-from xs (λ x₂ x₃ → all-to xs Pxs x₂ x₃)
  ≡⟨ cong (λ x₂ → x₁ ∷ x₂) (all-∀-from∘to xs Pxs) ⟩
    x₁ ∷ Pxs
  ∎

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

all-∀-to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (f : (∀ x → x ∈ xs → P x)) → all-to xs (all-from xs f) ≡ f   
all-∀-to∘from [] f =
  begin
    all-to [] (all-from [] f)
  ≡⟨⟩
    all-to [] []
  ≡⟨⟩
    ∀-extensionality λ x → ∀-extensionality λ{ ()}

all-∀-to∘from (x ∷ xs) f = ∀-extensionality λ x₁ → extensionality λ{ (here refl) → refl ; (there x₂) → Eq.cong-app (Eq.cong-app (all-∀-to∘from xs λ x₃ x₄ → f x₃ (there x₄)) x₁) x₂}
    
all-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs ≃ ∀ x → x ∈ xs → P x
all-∀ xs = record { to = all-to xs ; from = all-from xs ; from∘to = all-∀-from∘to xs; to∘from = all-∀-to∘from xs }

-----------------------------------------------------------------------------------------------------------------------------------------------
all-ex-to : ∀ {A : Set} {P : A → Set} (xs : List A) → Any P xs → ∃[ x ] (x ∈ xs × P x)
all-ex-to (x ∷ xs) (here x₁) = ⟨ x , ⟨ here refl , x₁ ⟩ ⟩
all-ex-to (x ∷ xs) (there anyPxs) with all-ex-to xs anyPxs
... | ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ there fst₁ , snd ⟩ ⟩

all-ex-from : ∀ {A : Set} {P : A → Set} (xs : List A) → ∃[ x ] (x ∈ xs × P x) → Any P xs
all-ex-from (x ∷ xs) ⟨ .x , ⟨ here refl , snd ⟩ ⟩ = here snd
all-ex-from (x ∷ xs) ⟨ fst , ⟨ there fst₁ , snd ⟩ ⟩ = there (all-ex-from xs ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩)

all-∃-from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (x : Any P xs) → all-ex-from xs (all-ex-to xs x) ≡ x
all-∃-from∘to (x₁ ∷ xs) (here x) = refl
all-∃-from∘to (x₁ ∷ xs) (there anyPxs) = 
  begin
    all-ex-from (x₁ ∷ xs) (all-ex-to (x₁ ∷ xs) (there anyPxs))
  ≡⟨ cong ( λ Pxs′ → there Pxs′) (all-∃-from∘to xs anyPxs) ⟩
    there anyPxs
  ∎

all-∃-to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (∃x : ∃[ x ] (x ∈ xs × P x)) → all-ex-to xs (all-ex-from xs ∃x) ≡ ∃x
all-∃-to∘from (x ∷ xs) ⟨ .x , ⟨ here refl , snd ⟩ ⟩ = refl
all-∃-to∘from (x ∷ xs) ⟨ fst , ⟨ there fst₁ , snd ⟩ ⟩ =
  begin
    all-ex-to (x ∷ xs) (all-ex-from (x ∷ xs) (⟨ fst , ⟨ there fst₁ , snd ⟩ ⟩))
  ≡⟨⟩
    all-ex-to (x ∷ xs) (there (all-ex-from xs ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩))
  ≡⟨ cong (λ (⟨ y , ⟨ y∈xs , Py ⟩ ⟩) → ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩) (all-∃-to∘from xs ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩) ⟩
    ⟨ fst , ⟨ there fst₁ , snd ⟩ ⟩
  ∎

all-∃ : ∀ {A : Set} {P : A → Set} (xs : List A) → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
all-∃ xs = record { to = all-ex-to xs
                  ; from = all-ex-from xs
                  ; from∘to = all-∃-from∘to xs
                  ; to∘from = all-∃-to∘from xs
                  }


-----------------------------------------------------------------------------------------------------------------------------------------------
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
any? P? [] = no λ{ ()}
any? P? (x ∷ xs) with P? x | any? P? xs
... | yes Px | _ = yes (here Px)
... | no ¬Px | yes anyP = yes (there anyP)
... | no ¬Px | no ¬anyP = no λ{ (here x) → ¬Px x ; (there x₁) → ¬anyP x₁}

-----------------------------------------------------------------------------------------------------------------------------------------------

data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )

split P? [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩

split P? (x ∷ zs) with P? x | split P? zs
... | yes Px | ⟨ xs , ⟨ ys , ⟨ merge , ⟨ AllPxs , All¬Pys ⟩ ⟩ ⟩ ⟩ = ⟨ (x ∷ xs) , ⟨ ys , ⟨ left-∷ merge , ⟨ Px ∷ AllPxs , All¬Pys ⟩ ⟩ ⟩ ⟩
... | no ¬Px | ⟨ xs , ⟨ ys , ⟨ merge , ⟨ AllPxs , All¬Pys ⟩ ⟩ ⟩ ⟩ = ⟨ xs , ⟨ (x ∷ ys) , ⟨ right-∷ merge , ⟨ AllPxs , (λ x₁ → ¬Px x₁) ∷ All¬Pys ⟩ ⟩ ⟩ ⟩

¬z≡n : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡n ()

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero  ≡ℕ? zero                = yes refl
zero  ≡ℕ? suc n               = no ¬z≡n
suc m ≡ℕ? zero                = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes refl = yes refl
...                | no ¬m≡n  = no (¬s≡s ¬m≡n)

_ : split (_≡ℕ? 3) [ 3 , 0 , 3 , 1 ]
  ≡ ⟨ [ 3 , 3 ] , ⟨ [ 0 , 1 ] , ⟨ (left-∷ (right-∷ (left-∷ (right-∷ [])))) , ⟨ refl ∷ refl ∷ [] , ¬z≡n ∷ (¬s≡s ¬z≡n) ∷ [] ⟩ ⟩ ⟩ ⟩ 
_ = refl
