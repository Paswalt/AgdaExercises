import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

-- Induction corresponds to recursive functions!
-- Showing the ∀ corresponds to a FUNCTION that, given
-- arguments m n p, returns the specific evidence for
-- that instance!

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    (suc (m + n)) + p
  ≡⟨⟩
    suc (m + n + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎


-- We show commutativity for addition. For this we need the following lemma:
+neutral : ∀ n → n + zero ≡ n
+neutral zero = refl
+neutral (suc n) =
  begin
    suc n + zero
  ≡⟨⟩
    suc (n + zero)
  ≡⟨ cong suc (+neutral n) ⟩
    suc n
  ∎

+rightrec : ∀ (n m : ℕ) → n + suc m ≡ suc (n + m)
+rightrec zero m = refl
+rightrec (suc n) m = cong suc (+rightrec n m)

-- The final proof:
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+neutral n)
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+rightrec n m) ⟩
    n + suc m
  ∎

-- Corollary:
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎

------------------------------------Exercises--------------------------------------------
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

*-distr-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distr-+ zero n p = refl
*-distr-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_ ) (*-distr-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m) * p + n * p
  ∎


*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distr-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_ ) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    suc m * (n * p)
  ∎


-- For this one we need lemma again

*neutral : ∀ n → n * zero ≡ zero
*neutral zero = refl
*neutral (suc n) = *neutral n

*one : ∀ n → n * (suc zero) ≡ n
*one zero = refl
*one (suc n) =  cong suc (*one n)

*comm-suc : ∀ (m n : ℕ) → m * 1 + m * n ≡ m * suc n
*comm-suc zero n = refl
*comm-suc (suc m) n =
  begin
    suc m * 1 + suc m * n
  ≡⟨⟩
    (1 + (m * 1)) + (n + (m * n))
  ≡⟨ cong ( _+ (n + (m * n))) (+-comm 1 (m * 1)) ⟩
    ((m * 1) + 1) + (n + (m * n))
  ≡⟨ +-assoc (m * 1) 1 (n + (m * n)) ⟩
    (m * 1) + (1 + (n + (m * n)))
  ≡⟨ cong ((m * 1) +_) (sym (+-assoc 1 n (m * n))) ⟩
    (m * 1) + ((1 + n) + (m * n))
  ≡⟨ cong ((m * 1) +_) (+-comm (1 + n) (m * n)) ⟩
    (m * 1) + ((m * n) + (1 + n))
  ≡⟨ sym (+-assoc (m * 1) (m * n) (1 + n)) ⟩
    ((m * 1) + (m * n)) + (1 + n)
  ≡⟨ cong ( _+ (1 + n)) (*comm-suc m n) ⟩
    (m * suc n) + (1 + n)
  ≡⟨ +-comm (m * suc n) (1 + n) ⟩
    (1 + n) + (m * suc n)
  ≡⟨⟩
    suc m * suc n
  ∎

*comm : ∀ (m n : ℕ) → m * n ≡ n * m
*comm zero n =  sym (*neutral n)
*comm (suc m) n =
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (n +_) (*comm m n) ⟩
    n + n * m
  ≡⟨ cong (_+ (n * m)) (sym (*one n)) ⟩
    n * (suc zero) + n * m
  ≡⟨ *comm-suc n m ⟩
    n * suc m
  ∎

-- No induction needed because it follows from the definition of ∸
∸zero : ∀ n → zero ∸ n ≡ zero
∸zero zero = refl
∸zero (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p = ∸zero p
∸-+-assoc (suc m) (suc n) p =
  begin
    suc m ∸ suc n ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
  ≡⟨⟩
    refl


-------------------------Stretch exercises.........................................
^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-comm (m ^ p) zero = refl
^-distribˡ-+-* m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m ^ (suc (n + p))
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * m ^ n * m ^ p
  ≡⟨⟩
    m ^ (suc n) * m ^ p
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ (suc p)
  ≡⟨⟩
    (m * n) * ((m * n) ^ p)
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    (m * n) * (m ^ p * n ^ p)
  ≡⟨ cong ( _* (m ^ p * n ^ p)) (*comm m n) ⟩
    (n * m) * (m ^ p * n ^ p)
  ≡⟨ sym (*-assoc (n * m) (m ^ p) (n ^ p)) ⟩
    (n * m) * m ^ p * n ^ p
  ≡⟨ cong ( _* n ^ p) (*-assoc n m (m ^ p)) ⟩
    n * (m * m ^ p) * n ^ p
  ≡⟨⟩
    n * m ^ suc p * n ^ p
  ≡⟨ cong (_* (n ^ p)) (*comm n (m ^ suc p)) ⟩
    m ^ suc p * n * n ^ p
  ≡⟨ *-assoc (m ^ suc p) n (n ^ p) ⟩
    m ^ suc p * (n * n ^ p)
  ≡⟨⟩
    m ^ suc p * n ^ suc p
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *comm n zero = refl
^-*-assoc m n (suc p) =
  begin
    (m ^ n) ^ suc p
  ≡⟨⟩
    (m ^ n) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
    m ^ (n + (n * p))
  ≡⟨ cong (m ^_) ( cong (n +_) (*comm n p)) ⟩
    m ^ (n + (p * n))
  ≡⟨⟩
    m ^ (suc p * n)
  ≡⟨ cong (m ^_) (*comm (suc p) n) ⟩
    m ^ (n * suc p)
  ∎
    


    
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

-- The first law holds. Proof:
shift : ∀ (b : Bin) → (from b) + (from b) ≡ (from (b O))
shift ⟨⟩ = refl
shift (b O) rewrite +-comm (from b + (from b + zero)) zero = refl
shift (b I) rewrite +-comm (suc (from b + (from b + 0))) zero = refl

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
    
