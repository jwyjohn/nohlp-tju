import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

-- Universals

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  -----------------
  → B M
∀-elim L M = L M

-- Exercise ∀-distrib-× (recommended)
-- Show that universals distribute over conjunction:

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
  { to      = λ x → ⟨ (λ x₁ → proj₁ (x x₁)) , (λ x₁ → proj₂ (x x₁)) ⟩
  ; from    = λ x x₁ → ⟨ (proj₁ x x₁) , (proj₂ x x₁) ⟩
  ; from∘to = λ x → refl
  ; to∘from = λ y → refl
  }

-- Exercise ⊎∀-implies-∀⊎ (practice)
-- Show that a disjunction of universals implies a universal of disjunctions:

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ x x₁ = case-⊎ (λ x₂ → inj₁ (x₂ x₁)) (λ x₂ → inj₂ (x₂ x₁)) x

-- Does the converse hold? If so, prove; if not, explain why.

-- Exercise ∀-× (practice)
-- Consider the following type.

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- Let B be a type indexed by Tri,
-- that is B : Tri → Set.
-- Show that ∀ (x : Tri) → B x is isomorphic to B aa × B bb × B cc.
-- Hint: you will need to postulate a version of extensionality that works for dependent functions.

-- Existentials
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
-- We define a convenient syntax for existentials as follows:
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- Equivalently, we could also declare existentials as a record type:
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

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

-- Exercise ∃-distrib-⊎ (recommended)
-- Show that existentials distribute over disjunction:
∃-distrib-⊎-to : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) → (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎-to ⟨ x , inj₁ y ⟩ = inj₁ ⟨ x , y ⟩
∃-distrib-⊎-to ⟨ x , inj₂ y ⟩ = inj₂ ⟨ x , y ⟩

∃-distrib-⊎-from : ∀ {A : Set} {B C : A → Set} →
  (∃[ x ] B x) ⊎ (∃[ x ] C x) → ∃[ x ] (B x ⊎ C x)
∃-distrib-⊎-from (inj₁ ⟨ x , x₁ ⟩) = ⟨ x , inj₁ x₁ ⟩
∃-distrib-⊎-from (inj₂ ⟨ x , x₁ ⟩) = ⟨ x , inj₂ x₁ ⟩

∃-distrib-⊎-from∘to : ∀ {A : Set} {B C : A → Set} →
  (x : ∃-syntax (λ x₁ → B x₁ ⊎ C x₁)) →
  ∃-distrib-⊎-from (∃-distrib-⊎-to x) ≡ x
∃-distrib-⊎-from∘to ⟨ x , inj₁ x₁ ⟩ = refl
∃-distrib-⊎-from∘to ⟨ x , inj₂ y ⟩ = refl

∃-distrib-⊎-to∘from : ∀ {A : Set} {B C : A → Set} →
  (y : ∃-syntax B ⊎ ∃-syntax C) →
  ∃-distrib-⊎-to (∃-distrib-⊎-from y) ≡ y
∃-distrib-⊎-to∘from (inj₁ ⟨ x , x₁ ⟩) = refl
∃-distrib-⊎-to∘from (inj₂ ⟨ x , x₁ ⟩) = refl

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
  { to      = ∃-distrib-⊎-to
  ; from    = ∃-distrib-⊎-from
  ; from∘to = ∃-distrib-⊎-from∘to
  ; to∘from = ∃-distrib-⊎-to∘from
  }

-- Exercise ∃×-implies-×∃ (practice)
-- Show that an existential of conjunctions implies a conjunction of existentials:
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
-- Does the converse hold? If so, prove; if not, explain why.

-- Exercise ∃-⊎ (practice)
-- Let Tri and B be as in Exercise ∀-×.
-- Show that ∃[ x ] B x is isomorphic to B aa ⊎ B bb ⊎ B cc.


-- An existential example
-- Recall the definitions of even and odd from Chapter Relations:
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)

-- we will show:
-- even n iff ∃[ m ] ( m * 2 ≡ n)
-- odd n iff ∃[ m ] (1 + m * 2 ≡ n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)


-- Exercise ∃-even-odd (practice)
-- How do the proofs become more difficult if we replace m * 2 and 1 + m * 2 by 2 * m and 2 * m + 1?
-- Rewrite the proofs of ∃-even and ∃-odd when restated in this way.

-- Exercise ∃-+-≤ (practice)
-- Show that y ≤ z holds if and only if there exists a x such that x + y ≡ z.


-- Existentials, Universals, and Negation
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
  { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
  ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
  ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
  ; to∘from =  λ{ ∀¬xy → refl }
  }

-- Exercise ∃¬-implies-¬∀ (recommended)
-- Show that existential of a negation implies negation of a universal:

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
  --------------
  → ¬ (∀ x → B x)

∃¬-implies-¬∀ ⟨ x , x₁ ⟩ = λ x₂ → x₁ (x₂ x)
