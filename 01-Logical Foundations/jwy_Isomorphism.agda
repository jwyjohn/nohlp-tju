import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Lambda expressions
-- λ{ P₁ → N₁; ⋯ ; Pₙ → Nₙ }
-- λ x → N
-- λ (x : A) → N

-- Function composition
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

-- Extensionality
-- Extensionality asserts that the only way to distinguish functions is by applying them;
-- if two functions applied to the same argument always yield the same result,
-- then they are the same function.
-- It is the converse of cong-app, as introduced earlier.
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    -----------------------
    → f ≡ g

-- Examples from Naturals
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)
-- Applying commutativity,
-- it is easy to show that both operators always
-- return the same result given the same arguments:
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
    helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
    helper m zero    = refl
    helper m (suc n) = cong suc (helper m n)
-- However, it might be convenient to assert that
-- the two operators are actually indistinguishable.
-- This we can do via two applications of extensionality:
same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))


-- Isomorphism
-- Two sets are isomorphic if they are in one-to-one correspondence.
-- Here is a formal definition of isomorphism:
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_


data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
    ∀ (from : B → A) →
    ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
    ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
    A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

≃-refl : ∀ {A : Set}
  -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }

≃-sym : ∀ {A B : Set}
  → A ≃ B
  -----
  → B ≃ A
≃-sym A≃B =
  record
  { to      = from A≃B
  ; from    = to   A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
  -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
  { to       = to   B≃C ∘ to   A≃B
  ; from     = from A≃B ∘ from B≃C
  ; from∘to  = λ{x →
    begin
      (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
    ≡⟨⟩
      from A≃B (from B≃C (to B≃C (to A≃B x)))
    ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
      from A≃B (to A≃B x)
    ≡⟨ from∘to A≃B x ⟩
    x
    ∎}
  ; to∘from = λ{y →
    begin
      (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
    ≡⟨⟩
      to B≃C (to A≃B (from A≃B (from B≃C y)))
    ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
      to B≃C (from B≃C y)
    ≡⟨ to∘from B≃C y ⟩
      y
    ∎}
  }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
    -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
    -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
    -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
  { to      = λ{x → to   B≲C (to   A≲B x)}
  ; from    = λ{y → from A≲B (from B≲C y)}
  ; from∘to = λ{x →
    begin
      from A≲B (from B≲C (to B≲C (to A≲B x)))
    ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
      from A≲B (to A≲B x)
    ≡⟨ from∘to A≲B x ⟩
      x
    ∎}
  }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
  -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
  { to      = to A≲B
  ; from    = from A≲B
  ; from∘to = from∘to A≲B
  ; to∘from = λ{y →
    begin
      to A≲B (from A≲B y)
    ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
      to A≲B (to B≲A y)
    ≡⟨ cong-app to≡from (to B≲A y) ⟩
      from B≲A (to B≲A y)
    ≡⟨ from∘to B≲A y ⟩
      y
    ∎}
  }

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
    -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
    -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
    -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercise ≃-implies-≲ (practice)
-- Show that every isomorphism implies an embedding.
≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
  -----
  → A ≲ B
≃-implies-≲ A≃B =
  record
  { to    = λ {x → (to A≃B x)}
  ; from  = λ {x → (from A≃B x)}
  ; from∘to  = λ {x → (from∘to A≃B x)}
  }

-- Exercise _⇔_ (practice)
-- Define equivalence of propositions
-- (also known as “if and only if”) as follows:
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

-- 一路 c-r c-r, c-c c-a
⇔-refl : ∀ {A : Set}
  -----
  → A ⇔ A
⇔-refl =
  record
  { to      = λ x → x
  ; from    = λ x → x
  }

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
  -----
  → B ⇔ A
⇔-sym A⇔B =
  record
  { to      = λ x → _⇔_.from A⇔B x
  ; from    = λ x → _⇔_.to A⇔B x
  }

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
  -----
  → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
  { to    = λ x → _⇔_.to B⇔C (_⇔_.to A⇔B x)
  ; from  = λ x → _⇔_.from A⇔B (_⇔_.from B⇔C x)
  }

