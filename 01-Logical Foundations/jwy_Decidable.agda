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
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

-- Evidence vs Computation
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
    --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    -------------
    → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

-- An alternative, which may seem more familiar, is to define a type of booleans:
data Bool : Set where
  true  : Bool
  false : Bool

-- Given booleans, we can define a function of two numbers
-- that computes to true if the comparison holds and to false otherwise:
infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n

_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎

-- Relating evidence and computation
T : Bool → Set
T true   =  ⊤
T false  =  ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    n       tt  =  z≤n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n        =  tt
≤→≤ᵇ (s≤s m≤n)  =  ≤→≤ᵇ m≤n


-- The best of both worlds
-- It is called Dec A, where Dec is short for decidable:
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

-- Exercise _<?_ (recommended)
-- Analogous to the function above, define a function to decide strict inequality:
¬n<z : ∀ {m : ℕ} → ¬ (m < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero  <? suc n               =  yes z<s
n     <? zero                =  no ¬n<z
suc m <? suc n with m <? n
...               | yes m<n  =  yes (s<s m<n)
...               | no ¬m<n  =  no (¬s<s ¬m<n)

-- Exercise _≡ℕ?_ (practice)
-- Define a function to decide whether two naturals are equal:
s≡s : ∀ {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
s≡s refl = refl

s≢s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
s≢s m≢n refl = m≢n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero  ≡ℕ? zero  = yes refl
zero ≡ℕ? suc n  = no λ ()
suc m ≡ℕ? zero  = no λ ()
suc n ≡ℕ? suc m with n ≡ℕ? m
...                | yes m≡n = yes (s≡s m≡n)
...                | no  m≢n = no  (s≢s m≢n)

-- Decidables from booleans, and booleans from decidables

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p


-- Erasure takes a decidable value to a boolean:
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false

-- Using erasure, we can easily derive _≤ᵇ_ from _≤?_:
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

-- Further, if D is a value of type Dec A,
-- then T ⌊ D ⌋ is inhabited exactly when A is inhabited:
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

-- Using these, we can easily derive that
-- T (m ≤ᵇ′ n) is inhabited exactly when m ≤ n is inhabited:
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness


-- Logical connectives
-- Most readers will be familiar with the logical connectives for booleans.
-- Each of these extends to decidables.

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x

-- There is also a slightly less familiar connective,
-- corresponding to implication:
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))

-- Exercise erasure (practice)
-- Show that erasure relates corresponding boolean and decidable operations:

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋

∧-× (yes x) (yes x₁) = refl
∧-× (yes x) (no x₁) = refl
∧-× (no x) (yes x₁) = refl
∧-× (no x) (no x₁) = refl
∨-⊎ (yes x) (yes x₁) = refl
∨-⊎ (yes x) (no x₁) = refl
∨-⊎ (no x) (yes x₁) = refl
∨-⊎ (no x) (no x₁) = refl
not-¬ (yes x) = refl
not-¬ (no x) = refl

-- Exercise iff-erasure (recommended)
-- Give analogues of the _⇔_ operation from Chapter Isomorphism,
-- operation on booleans and decidables,
-- and also show the corresponding erasure:
postulate
  _iff_ : Bool → Bool → Bool
  _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
  iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋


-- Proof by reflection

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

_ : 5 - 3 ≡ 2
_ = refl

True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋

-- Exercise False (practice)
-- Give analogues of True, toWitness, and fromWitness which work with negated properties.
-- Call these False, toWitnessFalse, and fromWitnessFalse.

False : ∀ {Q} → Dec (¬ Q) → Set
False {Q} = λ x → Q

toWitnessFalse : ∀ {A : Set} {D : Dec (¬ A)} → T ⌊ D ⌋ → (¬ A)
toWitnessFalse {A} {yes x} tt  =  x
toWitnessFalse {A} {no ¬x} ()
