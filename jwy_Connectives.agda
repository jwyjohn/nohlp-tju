import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning


-- Conjunction is product
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
    -------
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
  -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
  -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

-- In particular, product is commutative and associative up to isomorphism.
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
  { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
  ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
  ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
  { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
  ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
  ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
  ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
  }

-- Exercise ⇔≃× (recommended)
-- Show that A ⇔ B as defined earlier is isomorphic to (A → B) × (B → A).
⇔≃× : ∀ {A B : Set} → A ⇔ B  ≃ (A → B) × (B → A)
⇔≃× =
  record
  { to      = λ x → ⟨ _⇔_.to x , _⇔_.from x ⟩
  ; from    = λ y → record { to = proj₁ y ; from = proj₂ y }
  ; from∘to = λ x → refl
  ; to∘from = λ y → η-× y
  }

-- Truth is unit
data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = _

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
  { to      = λ{ ⟨ tt , x ⟩ → x }
  ; from    = λ{ x → ⟨ tt , x ⟩ }
  ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
  ; to∘from = λ{ x → refl }
  }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎


-- Disjunction is sum
data _⊎_ (A B : Set) : Set where

  inj₁ :
    A
    -----
    → A ⊎ B

  inj₂ :
    B
    -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5


-- Exercise ⊎-comm (recommended)
-- Show sum is commutative up to isomorphism.

-- Lemma  ⊎-2swap
⊎-2swap : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₂ inj₁ (case-⊎ inj₂ inj₁ w) ≡ w
⊎-2swap (inj₁ x) = refl
⊎-2swap (inj₂ x) = refl

⊎-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm =
  record
  { to      = λ x → case-⊎ inj₂ inj₁ x
  ; from    = λ y → case-⊎ inj₂ inj₁ y
  ; from∘to = λ x → ⊎-2swap x
  ; to∘from = λ y → ⊎-2swap y }



-- Exercise ⊎-assoc (practice)
-- Show sum is associative up to isomorphism.

-- Lemmas
⊎-assoc-to : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc-to = case-⊎ (case-⊎ inj₁ (inj₂ ∘ inj₁)) (inj₂ ∘ inj₂)

⊎-assoc-from : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-assoc-from =  case-⊎ (inj₁ ∘ inj₁) (case-⊎ (inj₁ ∘ inj₂) inj₂)

⊎-assoc-eql : ∀ {A B C : Set} → (x : (A ⊎ B) ⊎ C) → ⊎-assoc-from (⊎-assoc-to x) ≡ x
⊎-assoc-eql (inj₁ (inj₁ x)) = refl
⊎-assoc-eql (inj₁ (inj₂ x)) = refl
⊎-assoc-eql (inj₂ x) = refl

⊎-assoc-eqr : ∀ {A B C : Set} → (x : A ⊎ (B ⊎ C)) → ⊎-assoc-to (⊎-assoc-from x) ≡ x
⊎-assoc-eqr (inj₁ x) = refl
⊎-assoc-eqr (inj₂ (inj₁ x)) = refl
⊎-assoc-eqr (inj₂ (inj₂ x)) = refl


⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
  { to      = ⊎-assoc-to
  ; from    = ⊎-assoc-from
  ; from∘to = ⊎-assoc-eql
  ; to∘from = ⊎-assoc-eqr
  }

-- False is empty
data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
  --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- Exercise ⊥-identityˡ (recommended)
-- Show empty is the left identity of sums up to isomorphism.

-- Lemma
⊥-identityˡ-l1 : ∀ {A : Set} → (w : ⊥ ⊎ A) → inj₂ (case-⊎ ⊥-elim (λ x₁ → x₁) w) ≡ w
⊥-identityˡ-l1 (inj₂ x) = refl

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
  { to      = λ x → case-⊎ ⊥-elim (λ x₁ → x₁) x
  ; from    = λ x → inj₂ x
  ; from∘to = λ x → ⊥-identityˡ-l1 x
  ; to∘from = λ y → refl }

-- Exercise ⊥-identityʳ (practice)
-- Show empty is the right identity of sums up to isomorphism.

-- Lemma
⊥-identityˡ-l2 : ∀ {A : Set} → (w : A ⊎ ⊥ ) → inj₁ (case-⊎ (λ x₁ → x₁) ⊥-elim w) ≡ w
⊥-identityˡ-l2 (inj₁ x) = refl

⊥-identityʳ : ∀ {A : Set} →  A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
  { to      = λ x → case-⊎ (λ x₁ → x₁) ⊥-elim x
  ; from    = λ x → inj₁ x
  ; from∘to = λ x → ⊥-identityˡ-l2 x
  ; to∘from = λ y → refl }


-- Implication is function

-- In medieval times,
-- this rule was known by the name modus ponens.
-- It corresponds to function application.
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
  -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

-- Currying
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
  { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
  ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
  ; from∘to =  λ{ f → refl }
  ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
  }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
  { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
  ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
  ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
  ; to∘from = λ{ ⟨ g , h ⟩ → refl }
  }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
  { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
  ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
  ; to∘from = λ{ ⟨ g , h ⟩ → refl }
  }

-- Distribution
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
  { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
               ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
    }
  ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
               ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
    }
  ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
               ; ⟨ inj₂ y , z ⟩ → refl
    }
  ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
               ; (inj₂ ⟨ y , z ⟩) → refl
    }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
  { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
               ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
    }
  ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
               ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
               ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
    }
  ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
               ; (inj₂ z)         → refl
    }
  }


-- Exercise ⊎-weak-× (recommended)
-- Show that the following property holds:
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , x₁ ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , x₁ ⟩ = inj₂ ⟨ x , x₁ ⟩

-- Exercise ⊎×-implies-×⊎ (practice)
-- Show that a disjunct of conjuncts implies a conjunct of disjuncts:
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D)  → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , x₁ ⟩) = ⟨ (inj₁ x) , (inj₁ x₁) ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , x₁ ⟩) = ⟨ (inj₂ x) , (inj₂ x₁) ⟩

-- Does the converse hold? If so, prove; if not, give a counterexample.
-- No.
-- x : A × D ∈ (A ⊎ C) × (B ⊎ D) but ∉ (A × B) ⊎ (C × D)


