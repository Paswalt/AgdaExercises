import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import isomorphism using (_≃_; _⇔_; extensionality)

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

----------------------------------------------------------------------------------------------------

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
