-- First we define what a term can be according
-- to the following grammar
--  t ::=
--    true
--    false
--    zero
--    succ t
--    isZero t
--    pred t
--    if t then t else t

data Term : Set where
  true          : Term
  false         : Term
  zero          : Term
  succ          : Term → Term
  isZero        : Term → Term
  pred          : Term → Term
  if_then_else_ : Term → Term → Term → Term

-- Now we can define which terms are values according to the following
--  v ::=
--    true
--    false
--    nv
--  nv ::=
--    zero
--    succ nv

data IsNumValue : Term → Set where
  zero : IsNumValue zero
  succ : ∀ {t : Term} → IsNumValue t → IsNumValue (succ t)

data IsValue : Term → Set where
  true     : IsValue true
  false    : IsValue false
  numValue : ∀ {t : Term} → IsNumValue t → IsValue t

-- We can now define the small-step evaluation relation
data _⇒_ : Term → Term → Set where
  E-ifTrue : ∀ {t₂ t₃ : Term} → (if true then t₂ else t₃) ⇒ t₂
  E-ifFalse : ∀ {t₂ t₃ : Term} → (if false then t₂ else t₃) ⇒ t₃
  E-if : ∀ {t₁ t₁' t₂ t₃ : Term} → t₁ ⇒ t₁' → (if t₁ then t₂ else t₃) ⇒ (if t₁' then t₂ else t₃)
  E-succ : ∀ {t₁ t₁' : Term} → t₁ ⇒ t₁' → (succ t₁) ⇒ (succ t₁')
  E-predZero : (pred zero) ⇒ zero
  E-predSucc : ∀ {t₁ : Term} → IsNumValue t₁ → (pred (succ t₁)) ⇒ t₁
  E-pred : ∀ {t₁ t₁' : Term} → t₁ ⇒ t₁' → (pred t₁) ⇒ (pred t₁')
  E-isZeroZero : (isZero zero) ⇒ true
  E-isZeroSucc : ∀ {t₁ : Term} → IsNumValue t₁ → isZero (succ t₁) ⇒ false
  E-isZero : ∀ {t₁ t₁' : Term} → t₁ ⇒ t₁' → (isZero t₁) ⇒ (isZero t₁')

-- Now we can define the types that we want to support, in this
-- case only the primitive types Nat and Bool
data Type : Set where
  ℕ : Type
  𝔹 : Type

-- Now we can define our binary typing relation ⦂
data _⦂_ : Term → Type → Set where
  T-true   : true ⦂ 𝔹
  T-false  : false ⦂ 𝔹
  T-zero   : zero ⦂ ℕ
  T-succ   : ∀ {t₁ : Term} → t₁ ⦂ ℕ → (succ t₁) ⦂ ℕ
  T-pred   : ∀ {t₁ : Term} → t₁ ⦂ ℕ → (pred t₁) ⦂ ℕ
  T-isZero : ∀ {t₁ : Term} → t₁ ⦂ ℕ → (isZero t₁) ⦂ 𝔹
  T-if     : ∀ {t₁ t₂ t₃ : Term} {T : Type} → t₁ ⦂ 𝔹 → t₂ ⦂ T → t₃ ⦂ T → (if t₁ then t₂ else t₃) ⦂ T 

-- Now we can state the two main theorems, progress + preservation which together make up
-- type safety, meaning "well-typed terms" can not "go wrong", i.e. not get stuck in a normalform
-- that is not a value.

data ⊥ : Set where
  --we need negation for the proofs

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ A = (A → ⊥)

-- We need this to prove a contradiction because of how the values
-- are thrown together
num≢𝔹 : ∀ {t : Term} → (IsNumValue t) → ¬ (t ⦂ 𝔹)
num≢𝔹 zero ()
num≢𝔹 (succ ev) ()

-- We need this to show the succ step of preservation
inversion-lemma : ∀ {t : Term} → succ t ⦂ ℕ → t ⦂ ℕ
inversion-lemma (T-succ ev) = ev

data Progress : Term → Set where
  isValue : ∀ {t₁ : Term} → IsValue t₁ → Progress t₁
  isReducible : ∀ {t₁ t₁'} → t₁ ⇒ t₁' → Progress t₁

-- Because I am not defining the logical disjunction here we are going to use
-- a predicate for this as basically a logical connector
progress : ∀ {t : Term} {T : Type} → t ⦂ T  → Progress t
progress T-true = isValue true
progress T-false = isValue false
progress T-zero = isValue (numValue zero)
progress (T-succ t⦂T) with progress t⦂T
... | isValue (numValue x) = isValue (numValue (succ x))
... | isReducible red = isReducible (E-succ red)
progress (T-pred t⦂T) with progress t⦂T
... | isValue (numValue zero) = isReducible E-predZero
... | isValue (numValue (succ x)) = isReducible (E-predSucc x)
... | isReducible red = isReducible (E-pred red)
progress (T-isZero t⦂T) with progress t⦂T
... | isValue (numValue zero) = isReducible E-isZeroZero
... | isValue (numValue (succ x)) = isReducible (E-isZeroSucc x)
... | isReducible red = isReducible (E-isZero red)
progress (T-if t⦂T t⦂T₁ t⦂T₂) with progress t⦂T
... | isValue true = isReducible E-ifTrue
... | isValue false = isReducible E-ifFalse
... | isValue (numValue x) = ⊥-elim (num≢𝔹 x t⦂T)
... | isReducible red = isReducible (E-if red)

preservation : ∀{t t' : Term} {T : Type} → t ⦂ T → t ⇒ t' → t' ⦂ T
preservation (T-if t⦂T t⦂T₁ t⦂T₂) E-ifTrue = t⦂T₁
preservation (T-if t⦂T t⦂T₁ t⦂T₂) E-ifFalse = t⦂T₂
preservation (T-if t⦂T t⦂T₁ t⦂T₂) (E-if tt') = T-if (preservation t⦂T tt') t⦂T₁ t⦂T₂
preservation (T-succ t⦂T) (E-succ tt') = T-succ (preservation t⦂T tt')
preservation (T-pred t⦂T) E-predZero = T-zero
preservation (T-pred t⦂T) (E-predSucc x) = inversion-lemma t⦂T
preservation (T-pred t⦂T) (E-pred tt') = T-pred (preservation t⦂T tt')
preservation (T-isZero t⦂T) E-isZeroZero = T-true
preservation (T-isZero t⦂T) (E-isZeroSucc x) = T-false
preservation (T-isZero t⦂T) (E-isZero tt') = T-isZero (preservation t⦂T tt')
