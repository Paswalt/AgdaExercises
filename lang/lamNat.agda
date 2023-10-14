-- Trying to crecreate the lambda lecture on essentials of programming languages 2022 by myself without looking up
-- definitions for best learn effect

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Part I: Syntax and Semantics------------------------------------------------------------------------------------------------------------
-- Syntax
-- L M N ::=
--   x
--   ƛ x ⇒ N
--   L · M
--   `zero
--   `suc N
--   case L [ zero ⇒ N | suc x ⇒ M ]
--   rec f ⇒ x ⇒ t

Id : Set
Id = String

data Term : Set where
  `_    : Id → Term
  ƛ_⇒_  : Id → Term → Term
  _·_   : Term → Term → Term
  `zero : Term
  `suc  : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  rec_⇒_⇒_ : Id → Id → Term → Term


infix 10 `_
infix 9 `suc
infixl 8 _·_
infix 7 rec_⇒_⇒_
infix 6 ƛ_⇒_


-- Values
-- V ::=
--   `zero
--   `suc V
--   ƛ x ⇒ N

data Value : Term → Set where

  V-zero :
         -----------
         Value `zero

  V-suc : ∀ {t : Term}
        → Value t
        --------------
        → Value (`suc t)

  V-abs : ∀ {x : Id} {N : Term}
        -----------------------
        → Value (ƛ x ⇒ N)

  V-rec : ∀ {f x : Id} {N : Term}
        -------------------------
        → Value (rec f ⇒ x ⇒ N)

-- Substitution
-- We silently assume that M is a value, otherwise more
-- work would have needed to be done (α-conversion)
[_↦_]_ : Id → Term → Term → Term
[ y ↦ M ] (` x) with x ≟ y
... | yes _ = M
... | no  _ = ` x
[ y ↦ M ] (ƛ x ⇒ N) with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ [ y ↦ M ] N
[ y ↦ M ] (L · N) = ([ y ↦ M ] L) · ([ y ↦ M ] N)
[ y ↦ M ] `zero = `zero
[ y ↦ M ] `suc N = `suc ([ y ↦ M ] N)
[ y ↦ M ] case N [zero⇒ N₁ |suc x ⇒ N₂ ] with x ≟ y
... | yes _ = case ([ y ↦ M ] N) [zero⇒ ([ y ↦ M ] N₁) |suc x ⇒ N₂ ]
... | no  _ = case ([ y ↦ M ] N) [zero⇒ ([ y ↦ M ] N₁) |suc x ⇒ ([ y ↦ M ] N₂) ]
[ y ↦ M ] (rec f ⇒ x ⇒ N) with f ≟ y
... | yes _ = rec f ⇒ x ⇒ N
... | no  _ with x ≟ y
... | yes _ = rec f ⇒ x ⇒ N
... | no  _ = rec f ⇒ x ⇒ ([ y ↦ M ] N)

-- Smallstep evaluation relation —→

data _—→_ : Term → Term → Set where

  ξ-App1 : ∀ {L L' M : Term}
         → L —→ L'
         ------------------
         → (L · M) —→ (L' · M)
         
  ξ-App2 : ∀ {V M M' : Term}
         → Value V
         → M —→ M'
         -------------------
         → (V · M) —→ (V · M')

  β-AppAbs : ∀ {x : Id} {N V : Term}
           → Value V
           ----------------------------
           → ((ƛ x ⇒ N) · V) —→ ([ x ↦ V ] N)

  ξ-suc : ∀ {N N' : Term}
        → N —→ N'
        -----------------
        → (`suc N) —→ (`suc N')
        
  β-rec : ∀ {f x : Id} {N V : Term}
        → Value V
        ---------------------------
        → ((rec f ⇒ x ⇒ N) · V) —→ ((ƛ x ⇒ ([ f ↦ rec f ⇒ x ⇒ N ] N)) · V)

  ξ-case : ∀ {x : Id} {L L' M N : Term}
         → L —→ L'
         ---------------------
         → case L [zero⇒ M |suc x ⇒ N ] —→ case L' [zero⇒ M |suc x ⇒ N ] 

  β-zero : ∀ {x : Id} {L M N : Term}
         ---------------------------------------
         → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x : Id} {V M N : Term}
        → Value V
        ------------------------------------------------------
        → case (`suc V) [zero⇒ M |suc x ⇒ N ] —→ ([ x ↦ V ] N)


data _—↠_ : Term → Term → Set where
  ↠-refl  : ∀ {M : Term} → M —↠ M
  ↠-trans : ∀ {L M N : Term} → L —→ M → M —↠ N → L —↠ N

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ (`"s" · (`"s" · `"z"))

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

_ : (twoᶜ · sucᶜ · `zero) —↠ (`suc (`suc `zero))
_ = ↠-trans (ξ-App1 (β-AppAbs V-abs)) (↠-trans (β-AppAbs V-zero) (↠-trans (ξ-App2 V-abs (β-AppAbs V-zero)) (↠-trans (β-AppAbs (V-suc V-zero)) ↠-refl)))

-- Part II: Types and typing judgement------------------------------------------------------------------------------------------------------------
-- Types
--  T ::=
--    ℕ
--    T → T

data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type

-- For judgements about terms and types, because the language has
-- (free) variables, we need something called a context that carries environment
-- assumptions about typing judgements
data Context : Set where
  ∅ : Context
  _▸_⦂_ : Context → Id → Type → Context

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x T} → (Γ ▸ x ⦂ T) ∋ x ⦂ T
  S : ∀ {Γ x y T T'} → x ≢ y → Γ ∋ x ⦂ T →  (Γ ▸ y ⦂ T') ∋ x ⦂ T

-- Now we can start to define typing judgements to type different terms
data _⊢_⦂_ : Context → Term → Type → Set where
  T-var : ∀ {Γ x T}
        → Γ ∋ x ⦂ T
        -----------
        → Γ ⊢ ` x ⦂ T

  T-abs : ∀ {Γ x N T T'}
        → (Γ ▸ x ⦂ T) ⊢ N ⦂ T'
        ---------------------
        → Γ ⊢ (ƛ x ⇒ N) ⦂ (T ⇒ T')

  T-app : ∀ {Γ M N T T'}
        → Γ ⊢ M ⦂ (T ⇒ T')
        → Γ ⊢ N ⦂ T
        ------------------
        → Γ ⊢ (M · N) ⦂ T'

  T-zero : ∀ {Γ} → Γ ⊢ `zero ⦂ `ℕ

  T-suc : ∀ {Γ n}
        → Γ ⊢ n ⦂ `ℕ
        ------------
        → Γ ⊢ (`suc n) ⦂ `ℕ

  T-case : ∀ {Γ L x M N T}
         → Γ ⊢ L ⦂ `ℕ
         → Γ ⊢ M ⦂ T
         → (Γ ▸ x ⦂ `ℕ) ⊢ N ⦂ T
         ---------------
         → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ T

  T-rec : ∀ {Γ x f N T T'}
        → ((Γ ▸ f ⦂ (T ⇒ T')) ▸ x ⦂ T) ⊢ N ⦂ T'
        -------------------------------
        → Γ ⊢ (rec f ⇒ x ⇒ N) ⦂ (T ⇒ T')

-- Part III: Properties of the type system and language-------------------------------------------------------------------------------------------------
-- Lemma: Value are in normal form
value-nf : ∀ {M N : Term} → Value M → ¬ M —→ N
value-nf V-zero = λ{ ()}
value-nf (V-suc {t} vm) = λ{ (ξ-suc x) → value-nf vm x}
value-nf V-abs = λ{ ()}
value-nf V-rec = λ{ ()}

-- Theorem: Single-step evaluation is deterministic
—→determinacy : ∀ {L M N} → L —→ M → L —→ N → M ≡ N
—→determinacy (ξ-App1 LM) (ξ-App1 LN) rewrite —→determinacy LM LN = refl
—→determinacy (ξ-App1 LM) (ξ-App2 x LN) = ⊥-elim (value-nf x LM)
—→determinacy (ξ-App2 x LM) (ξ-App1 LN) = ⊥-elim (value-nf x LN)
—→determinacy (ξ-App2 x LM) (ξ-App2 x₁ LN) rewrite —→determinacy LM LN = refl
—→determinacy (ξ-App2 x LM) (β-AppAbs x₁) = ⊥-elim (value-nf x₁ LM)
—→determinacy (ξ-App2 x LM) (β-rec x₁) = ⊥-elim (value-nf x₁ LM)
—→determinacy (β-AppAbs x) (ξ-App2 x₁ LN) = ⊥-elim (value-nf x LN)
—→determinacy (β-AppAbs x) (β-AppAbs x₁) = refl
—→determinacy (ξ-suc LM) (ξ-suc LN) rewrite —→determinacy LM LN = refl
—→determinacy (β-rec x) (ξ-App2 x₁ LN) = ⊥-elim (value-nf x LN)
—→determinacy (β-rec x) (β-rec x₁) = refl
—→determinacy (ξ-case LM) (ξ-case LN) rewrite —→determinacy LM LN = refl
—→determinacy (ξ-case LM) (β-suc x) = ⊥-elim (value-nf (V-suc x) LM)
—→determinacy β-zero β-zero = refl
—→determinacy (β-suc x) (ξ-case LN) = ⊥-elim (value-nf (V-suc x) LN)
—→determinacy (β-suc x) (β-suc x₁) = refl

-- Theorem: Progress

data Progress : Term → Set where
  isValue   : ∀ {t : Term} → Value t → Progress t
  canReduce : ∀ {t t' : Term} → t —→ t' → Progress t

progress : ∀ {t T} → ∅ ⊢ t ⦂ T → Progress t
progress (T-abs ∅⊢t⦂T) = isValue V-abs
progress (T-app ∅⊢t⦂T ∅⊢t⦂T₁) with progress ∅⊢t⦂T | progress ∅⊢t⦂T₁
... | isValue V-abs | isValue b = canReduce (β-AppAbs b)
... | isValue V-rec | isValue b = canReduce (β-rec b)
... | isValue a | canReduce b = canReduce (ξ-App2 a b)
... | canReduce a | isValue b = canReduce (ξ-App1 a)
... | canReduce a | canReduce b = canReduce (ξ-App1 a)
progress T-zero = isValue V-zero
progress (T-suc ∅⊢t⦂T) with progress ∅⊢t⦂T
... | isValue v = isValue (V-suc v)
... | canReduce red = canReduce (ξ-suc red)
progress (T-case {Γ} {L} {x} {M} {N} ∅⊢t⦂T ∅⊢t⦂T₁ ∅⊢t⦂T₂) with progress ∅⊢t⦂T
... | isValue V-zero = canReduce (β-zero {x} {N} {M})
... | isValue (V-suc v) = canReduce (β-suc v)
... | canReduce red = canReduce (ξ-case red)
progress (T-rec ∅⊢t⦂T) = isValue V-rec

-- Theorem: Preservation
-- For this we need more work. I will come back to this
