open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import plfa.part1.Isomorphism using (_≃_; extensionality; _∘_)

-- Negation
-- reductio ad absurdum
-- if assuming A leads to the conclusion ⊥ (an absurdity), then we must have ¬ A.
¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
  ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
  -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set}
  → A
  -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
  -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
  -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

-- It is trivial to show distinct numbers are not equal:
-- This is our first use of an absurd pattern in a lambda expression. 
_ : 1 ≢ 2
_ = λ()


-- Indeed, there is exactly one proof of ⊥ → ⊥.
-- We can write this proof two different ways:
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

-- Indeed, we can show any two proofs of a negation are equal:
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- Exercise <-irreflexive (recommended)
-- Using negation,
-- show that strict inequality is irreflexive,
-- that is, n < n holds for no n.
<-irreflexive : ∀ (n : ℕ) → n < n → ⊥
<-irreflexive (suc n) (Data.Nat.s≤s sn<sn) = <-irreflexive n sn<sn


-- Exercise trichotomy (practice)
-- Show that strict inequality satisfies trichotomy,
-- that is, for any naturals m and n exactly one of the following holds:
-- m < n
-- m ≡ n
-- m > n

-- Exercise ⊎-dual-× (recommended)
-- Show that conjunction, disjunction, and negation are related
-- by a version of De Morgan’s Law.
-- ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

⊎-dual-×-to : ∀ {A B : Set} →  ¬ (A ⊎ B) →  (¬ A) × (¬ B)
⊎-dual-×-to = λ x → (λ x₁ → x (inj₁ x₁)) , (λ x₁ → x (inj₂ x₁))

⊎-dual-×-from :  ∀ {A B : Set} →  (¬ A) × (¬ B) → ¬ (A ⊎ B)
⊎-dual-×-from = λ (a , b) x → case-⊎ a b x

⊎-dual-×-from∘to : ∀ {A B : Set} (x : ¬ (A ⊎ B)) → ⊎-dual-×-from (⊎-dual-×-to x) ≡ x
⊎-dual-×-from∘to x = assimilation (λ x₁ → case-⊎ (λ z → x (inj₁ z)) (λ z → x (inj₂ z)) x₁) (λ x₁ → x x₁)

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = record
  { to      = ⊎-dual-×-to
  ; from    = ⊎-dual-×-from
  ; from∘to = ⊎-dual-×-from∘to
  ; to∘from = λ y → refl
  }


-- Do we also have the following?
-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- If so, prove;
-- if not, can you give a relation weaker than isomorphism that relates the two sides?
-- ×-dual-⊎-to : ∀ {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
-- ×-dual-⊎-to x = {!!}

×-dual-⊎-from : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎-from = λ x (a , b) → case-⊎ (λ x₁ → x₁ a) (λ x₁ → x₁ b) x

-- ×-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- ×-dual-⊎ = record
--   { to      = ×-dual-⊎-to
--   ; from    = ×-dual-⊎-from
--   ; from∘to = {!!}
--   ; to∘from = {!!}
--   }

-- Intuitive and Classical logic

-- Excluded middle is irrefutable
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ (λ x → k (inj₁ x)))

-- Exercise Classical (stretch)
-- Consider the following principles:

-- Excluded Middle: A ⊎ ¬ A, for all A
-- Double Negation Elimination: ¬ ¬ A → A, for all A
-- Peirce’s Law: ((A → B) → A) → A, for all A and B.
-- Implication as disjunction: (A → B) → ¬ A ⊎ B, for all A and B.
-- De Morgan: ¬ (¬ A × ¬ B) → A ⊎ B, for all A and B.
-- Show that each of these implies all the others.


-- Exercise Stable (stretch)
-- Say that a formula is stable if double negation elimination holds for it:

Stable : Set → Set
Stable A = ¬ ¬ A → A

-- Show that any negated formula is stable,
-- and that the conjunction of two stable formulas is stable.

¬-stable : ∀ (A : Set) → Stable (¬ A)
¬-stable A = λ x x₁ → x (λ x₂ → x₂ x₁)
